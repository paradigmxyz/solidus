import EvmCompiler.Functions.AllocationInteractionFrame

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionFrameExecution

open AllocationInteractionRelation

namespace Code

theorem openRun_push (value : Word) (target : TargetState) :
    Structured.InteractionSemantics.Code.openRun [.push value] target =
      .done (.ok (StateRel.pushTargetBy 33 value target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  rfl

theorem openRun_mload
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
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.mload.continuingStep? = some .mload)
    (by simp) (by simp)]
  simp [Assembly.PrimStep.run, hStack, hLoad, EvmYul.Stack.pop,
    EvmYul.Stack.push,
    Simulation.Interaction.map, Simulation.Interaction.bind,
    Simulation.Interaction.pure,
    StateRel.contractTargetBy, Structured.RunState.withEVM,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem openRun_dup1
    {target : TargetState} {value : Word} {rest : List Word}
    (hStack : target.evm.stack = value :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .dup1] target =
      .done (.ok (StateRel.pushTarget value target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.dup1.continuingStep? = some (.dup 1))
    (by simp) (by simp)]
  simp [Assembly.PrimStep.run, hStack, EvmYul.dup, EvmYul.Stack.push,
    Simulation.Interaction.map, Simulation.Interaction.bind,
    Simulation.Interaction.pure, StateRel.pushTarget,
    StateRel.pushTargetBy, Structured.RunState.withEVM,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem openRun_dup2
    {target : TargetState} {first second : Word} {rest : List Word}
    (hStack : target.evm.stack = first :: second :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .dup2] target =
      .done (.ok (StateRel.pushTarget second target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.dup2.continuingStep? = some (.dup 2))
    (by simp) (by simp)]
  simp [Assembly.PrimStep.run, hStack, EvmYul.dup, EvmYul.Stack.push,
    Simulation.Interaction.map, Simulation.Interaction.bind,
    Simulation.Interaction.pure, StateRel.pushTarget,
    StateRel.pushTargetBy, Structured.RunState.withEVM,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem openRun_add
    {target : TargetState} {right left : Word} {rest : List Word}
    (hStack : target.evm.stack = right :: left :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .add] target =
      .done (.ok
        (StateRel.contractTargetBy 1 (EvmYul.UInt256.add right left)
          rest target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.add.continuingStep? =
      some (.bin EvmYul.UInt256.add)) (by simp) (by simp)]
  simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp, hStack,
    EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run,
    Simulation.Interaction.map, Simulation.Interaction.bind,
    Simulation.Interaction.pure, StateRel.contractTargetBy,
    Structured.RunState.withEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem openRun_sub
    {target : TargetState} {left right : Word} {rest : List Word}
    (hStack : target.evm.stack = left :: right :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .sub] target =
      .done (.ok
        (StateRel.contractTargetBy 1 (EvmYul.UInt256.sub left right)
          rest target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.sub.continuingStep? =
      some (.bin EvmYul.UInt256.sub)) (by simp) (by simp)]
  simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp, hStack,
    EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run,
    Simulation.Interaction.map, Simulation.Interaction.bind,
    Simulation.Interaction.pure, StateRel.contractTargetBy,
    Structured.RunState.withEVM, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem openRun_mstore
    {target : TargetState} {address value : Word} {rest : List Word}
    (hStack : target.evm.stack = address :: value :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .mstore] target =
      .done (.ok (StateRel.mstoreTarget address value rest target)) := by
  rw [Structured.InteractionSemantics.Code.openRun_single]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
    Structured.InteractionSemantics.BasicInstr.openStepEVM
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.mstore.continuingStep? =
      some (.binaryMachineState EvmYul.MachineState.mstore))
    (by simp) (by simp)]
  simp [Assembly.PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hStack,
    EvmYul.Stack.pop2, Id.run, Simulation.Interaction.map,
    Simulation.Interaction.bind, Simulation.Interaction.pure,
    StateRel.mstoreTarget, Structured.RunState.withEVM,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

end Code

open AllocationInteractionFrame

/-- Proof state produced by the compiler-owned allocator advance prefix. -/
def allocatorAdvanceTarget (config : Config) (depth : Nat)
    (target : TargetState) : TargetState :=
  let cellWord := AllocationSupport.word config.allocatorCell
  let baseWord := EvmYul.UInt256.ofNat (baseAt config depth)
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let nextWord := EvmYul.UInt256.add bytesWord baseWord
  let afterCell := StateRel.pushTargetBy 33 cellWord target
  let afterLoad :=
    StateRel.contractTargetBy 1 baseWord target.evm.stack afterCell
  let afterDup := StateRel.pushTarget baseWord afterLoad
  let afterBytes := StateRel.pushTargetBy 33 bytesWord afterDup
  let afterAdd :=
    StateRel.contractTargetBy 1 nextWord
      (baseWord :: target.evm.stack) afterBytes
  let afterCellStore := StateRel.pushTargetBy 33 cellWord afterAdd
  StateRel.mstoreTarget cellWord nextWord
    (baseWord :: target.evm.stack) afterCellStore

/-- Exact execution of the existing allocator-cell advance prefix. -/
theorem allocatorAdvance_openRun
    {config : Config} {depth : Nat} {target : TargetState}
    (hReady : AllocatorReady config depth target) :
    Structured.InteractionSemantics.Code.openRun
        [ .push (AllocationSupport.word config.allocatorCell),
          .op .mload, .op .dup1,
          .push (AllocationSupport.frameBytes config.frameWords),
          .op .add,
          .push (AllocationSupport.word config.allocatorCell),
          .op .mstore ] target =
      .done (.ok (allocatorAdvanceTarget config depth target)) := by
  let cellWord := AllocationSupport.word config.allocatorCell
  let baseWord := EvmYul.UInt256.ofNat (baseAt config depth)
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let nextWord := EvmYul.UInt256.add bytesWord baseWord
  let afterCell := StateRel.pushTargetBy 33 cellWord target
  let afterLoad :=
    StateRel.contractTargetBy 1 baseWord target.evm.stack afterCell
  let afterDup := StateRel.pushTarget baseWord afterLoad
  let afterBytes := StateRel.pushTargetBy 33 bytesWord afterDup
  let afterAdd :=
    StateRel.contractTargetBy 1 nextWord
      (baseWord :: target.evm.stack) afterBytes
  let afterCellStore := StateRel.pushTargetBy 33 cellWord afterAdd
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hAfterCellStack :
      afterCell.evm.stack = cellWord :: target.evm.stack := rfl
  have hLoad :
      afterCell.evm.toMachineState.mload cellWord =
        (baseWord, afterCell.evm.toMachineState) := by
    have hBaseLoad :=
      Compiler.MemoryRelation.mload_eq_lookup_of_end_le
        target.evm.toMachineState config.allocatorCell hCellAddress
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
    rw [hReady.allocatorAt] at hBaseLoad
    simpa [afterCell, cellWord, baseWord, AllocationSupport.word,
      StateRel.pushTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hBaseLoad
  have hAfterLoadStack :
      afterLoad.evm.stack = baseWord :: target.evm.stack := rfl
  have hAfterBytesStack :
      afterBytes.evm.stack =
        bytesWord :: baseWord :: baseWord :: target.evm.stack := rfl
  have hAfterCellStoreStack :
      afterCellStore.evm.stack =
        cellWord :: nextWord :: baseWord :: target.evm.stack := rfl
  calc
    Structured.InteractionSemantics.Code.openRun
        [ .push cellWord, .op .mload, .op .dup1,
          .push bytesWord, .op .add, .push cellWord, .op .mstore ] target =
      Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.push cellWord] target)
        (Structured.InteractionSemantics.Code.openRun
          [.op .mload, .op .dup1, .push bytesWord, .op .add,
            .push cellWord, .op .mstore]) := by
      simpa using
        Structured.InteractionSemantics.Code.openRun_append
          [.push cellWord]
          [.op .mload, .op .dup1, .push bytesWord, .op .add,
            .push cellWord, .op .mstore] target
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .mload, .op .dup1, .push bytesWord, .op .add,
          .push cellWord, .op .mstore] afterCell := by
            rw [Code.openRun_push cellWord target]
            rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.op .mload] afterCell)
        (Structured.InteractionSemantics.Code.openRun
          [.op .dup1, .push bytesWord, .op .add,
            .push cellWord, .op .mstore]) := by
      simpa using
        Structured.InteractionSemantics.Code.openRun_append
          [.op .mload]
          [.op .dup1, .push bytesWord, .op .add,
            .push cellWord, .op .mstore] afterCell
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .dup1, .push bytesWord, .op .add,
          .push cellWord, .op .mstore] afterLoad := by
            rw [Code.openRun_mload hAfterCellStack hLoad]
            rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.op .dup1] afterLoad)
        (Structured.InteractionSemantics.Code.openRun
          [.push bytesWord, .op .add, .push cellWord, .op .mstore]) := by
      simpa using
        Structured.InteractionSemantics.Code.openRun_append
          [.op .dup1]
          [.push bytesWord, .op .add, .push cellWord, .op .mstore]
          afterLoad
    _ = Structured.InteractionSemantics.Code.openRun
        [.push bytesWord, .op .add, .push cellWord, .op .mstore]
        afterDup := by
          rw [Code.openRun_dup1 hAfterLoadStack]
          rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun
          [.push bytesWord] afterDup)
        (Structured.InteractionSemantics.Code.openRun
          [.op .add, .push cellWord, .op .mstore]) := by
      simpa using
        Structured.InteractionSemantics.Code.openRun_append
          [.push bytesWord] [.op .add, .push cellWord, .op .mstore]
          afterDup
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .add, .push cellWord, .op .mstore] afterBytes := by
          rw [Code.openRun_push bytesWord afterDup]
          rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.op .add] afterBytes)
        (Structured.InteractionSemantics.Code.openRun
          [.push cellWord, .op .mstore]) := by
      simpa using
        Structured.InteractionSemantics.Code.openRun_append
          [.op .add] [.push cellWord, .op .mstore] afterBytes
    _ = Structured.InteractionSemantics.Code.openRun
        [.push cellWord, .op .mstore] afterAdd := by
          rw [Code.openRun_add hAfterBytesStack]
          rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.push cellWord] afterAdd)
        (Structured.InteractionSemantics.Code.openRun [.op .mstore]) := by
      simpa using
        Structured.InteractionSemantics.Code.openRun_append
          [.push cellWord] [.op .mstore] afterAdd
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .mstore] afterCellStore := by
          rw [Code.openRun_push cellWord afterAdd]
          rfl
    _ = .done (.ok (allocatorAdvanceTarget config depth target)) := by
      simpa [allocatorAdvanceTarget, cellWord, baseWord, bytesWord,
        nextWord, afterCell, afterLoad, afterDup, afterBytes, afterAdd,
        afterCellStore] using Code.openRun_mstore hAfterCellStoreStack

/-- Proof state produced by preallocating the last word of a scratch frame. -/
def framePreallocTarget (config : Config) (frameDepth : Nat)
    (rest : List Word) (target : TargetState) : TargetState :=
  match config.frameWords with
  | 0 => target
  | slot + 1 =>
      let frameWord := EvmYul.UInt256.ofNat (baseAt config frameDepth)
      let zeroWord := AllocationSupport.zeroWord
      let offsetWord := AllocationSupport.slotOffset slot
      let address := EvmYul.UInt256.add offsetWord frameWord
      let afterZero := StateRel.pushTargetBy 33 zeroWord target
      let afterDup := StateRel.pushTarget frameWord afterZero
      let afterOffset := StateRel.pushTargetBy 33 offsetWord afterDup
      let afterAdd :=
        StateRel.contractTargetBy 1 address
          (zeroWord :: frameWord :: rest) afterOffset
      StateRel.mstoreTarget address zeroWord (frameWord :: rest) afterAdd

/-- Exact execution of the compiler-owned frame preallocation suffix. -/
theorem framePrealloc_openRun
    {config : Config} {frameDepth : Nat} {target : TargetState}
    {rest : List Word}
    (hPositive : 0 < config.frameWords)
    (hStack :
      target.evm.stack =
        EvmYul.UInt256.ofNat (baseAt config frameDepth) :: rest) :
    Structured.InteractionSemantics.Code.openRun
        (AllocationSupport.framePreallocCode config.frameWords) target =
      .done (.ok (framePreallocTarget config frameDepth rest target)) := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      let frameWord := EvmYul.UInt256.ofNat (baseAt config frameDepth)
      let zeroWord := AllocationSupport.zeroWord
      let offsetWord := AllocationSupport.slotOffset slot
      let address := EvmYul.UInt256.add offsetWord frameWord
      let afterZero := StateRel.pushTargetBy 33 zeroWord target
      let afterDup := StateRel.pushTarget frameWord afterZero
      let afterOffset := StateRel.pushTargetBy 33 offsetWord afterDup
      let afterAdd :=
        StateRel.contractTargetBy 1 address
          (zeroWord :: frameWord :: rest) afterOffset
      have hAfterZeroStack :
          afterZero.evm.stack = zeroWord :: frameWord :: rest := by
        simp [afterZero, StateRel.pushTargetBy, hStack, frameWord,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterDupStack :
          afterDup.evm.stack =
            frameWord :: zeroWord :: frameWord :: rest := by
        simp [afterDup, StateRel.pushTarget, StateRel.pushTargetBy,
          hAfterZeroStack, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterOffsetStack :
          afterOffset.evm.stack =
            offsetWord :: frameWord :: zeroWord :: frameWord :: rest := by
        simp [afterOffset, StateRel.pushTargetBy, hAfterDupStack,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterAddStack :
          afterAdd.evm.stack = address :: zeroWord :: frameWord :: rest := rfl
      simp only [AllocationSupport.framePreallocCode, hWords]
      calc
        Structured.InteractionSemantics.Code.openRun
            [.push zeroWord, .op .dup2, .push offsetWord,
              .op .add, .op .mstore] target =
          Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun
              [.push zeroWord] target)
            (Structured.InteractionSemantics.Code.openRun
              [.op .dup2, .push offsetWord, .op .add, .op .mstore]) := by
          simpa using Structured.InteractionSemantics.Code.openRun_append
            [.push zeroWord]
            [.op .dup2, .push offsetWord, .op .add, .op .mstore] target
        _ = Structured.InteractionSemantics.Code.openRun
            [.op .dup2, .push offsetWord, .op .add, .op .mstore]
            afterZero := by
          rw [Code.openRun_push zeroWord target]
          rfl
        _ = Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun
              [.op .dup2] afterZero)
            (Structured.InteractionSemantics.Code.openRun
              [.push offsetWord, .op .add, .op .mstore]) := by
          simpa using Structured.InteractionSemantics.Code.openRun_append
            [.op .dup2] [.push offsetWord, .op .add, .op .mstore]
            afterZero
        _ = Structured.InteractionSemantics.Code.openRun
            [.push offsetWord, .op .add, .op .mstore] afterDup := by
          rw [Code.openRun_dup2 hAfterZeroStack]
          rfl
        _ = Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun
              [.push offsetWord] afterDup)
            (Structured.InteractionSemantics.Code.openRun
              [.op .add, .op .mstore]) := by
          simpa using Structured.InteractionSemantics.Code.openRun_append
            [.push offsetWord] [.op .add, .op .mstore] afterDup
        _ = Structured.InteractionSemantics.Code.openRun
            [.op .add, .op .mstore] afterOffset := by
          rw [Code.openRun_push offsetWord afterDup]
          rfl
        _ = Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun [.op .add] afterOffset)
            (Structured.InteractionSemantics.Code.openRun [.op .mstore]) := by
          simpa using Structured.InteractionSemantics.Code.openRun_append
            [.op .add] [.op .mstore] afterOffset
        _ = Structured.InteractionSemantics.Code.openRun
            [.op .mstore] afterAdd := by
          rw [Code.openRun_add hAfterOffsetStack]
          rfl
        _ = .done (.ok
            (framePreallocTarget config frameDepth rest target)) := by
          simpa [framePreallocTarget, hWords, frameWord, zeroWord,
            offsetWord, address, afterZero, afterDup, afterOffset,
            afterAdd] using Code.openRun_mstore hAfterAddStack

def scratchFrameAcquireTarget (config : Config) (depth : Nat)
    (target : TargetState) : TargetState :=
  framePreallocTarget config depth target.evm.stack
    (allocatorAdvanceTarget config depth target)

@[simp] theorem scratchFrameAcquireTarget_returns
    (config : Config) (depth : Nat) (target : TargetState) :
    (scratchFrameAcquireTarget config depth target).returns = target.returns := by
  cases hWords : config.frameWords with
  | zero =>
      simp [scratchFrameAcquireTarget, framePreallocTarget,
        allocatorAdvanceTarget, hWords, StateRel.pushTargetBy,
        StateRel.pushTarget, StateRel.contractTargetBy,
        StateRel.mstoreTarget]
  | succ slot =>
      simp [scratchFrameAcquireTarget, framePreallocTarget,
        allocatorAdvanceTarget, hWords, StateRel.pushTargetBy,
        StateRel.pushTarget, StateRel.contractTargetBy,
        StateRel.mstoreTarget]

/-- Exact canonical execution of the emitted scratch-frame acquire code. -/
theorem scratchFrameAcquire_openRun
    {config : Config} {depth : Nat} {target : TargetState}
    (hPositive : 0 < config.frameWords)
    (hReady : AllocatorReady config depth target) :
    Structured.InteractionSemantics.Code.openRun
        (AllocationSupport.scratchFrameAcquireCode config) target =
      .done (.ok (scratchFrameAcquireTarget config depth target)) := by
  have hAdvance := allocatorAdvance_openRun hReady
  have hAdvanceStack :
      (allocatorAdvanceTarget config depth target).evm.stack =
        EvmYul.UInt256.ofNat (baseAt config depth) :: target.evm.stack := rfl
  have hPrealloc := framePrealloc_openRun hPositive hAdvanceStack
  unfold AllocationSupport.scratchFrameAcquireCode
  rw [Structured.InteractionSemantics.Code.openRun_append, hAdvance]
  simpa [scratchFrameAcquireTarget] using hPrealloc

/-- Concrete target state produced by the emitted frame-release sequence. -/
def scratchFrameReleaseTarget (config : Config) (depth : Nat)
    (target : TargetState) : TargetState :=
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let cellWord := AllocationSupport.word config.allocatorCell
  let currentWord := EvmYul.UInt256.ofNat (baseAt config (depth + 1))
  let priorWord := EvmYul.UInt256.ofNat (baseAt config depth)
  let afterBytes := StateRel.pushTargetBy 33 bytesWord target
  let afterCell := StateRel.pushTargetBy 33 cellWord afterBytes
  let afterLoad :=
    StateRel.contractTargetBy 1 currentWord
      (bytesWord :: target.evm.stack) afterCell
  let afterSub :=
    StateRel.contractTargetBy 1 priorWord target.evm.stack afterLoad
  let afterCellStore := StateRel.pushTargetBy 33 cellWord afterSub
  StateRel.mstoreTarget cellWord priorWord target.evm.stack afterCellStore

/-- Exact canonical execution of the emitted scratch-frame release code. -/
theorem scratchFrameRelease_openRun
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth)
    (hReady : AllocatorReady config (depth + 1) target) :
    Structured.InteractionSemantics.Code.openRun
        (AllocationSupport.scratchFrameReleaseCode config) target =
      .done (.ok (scratchFrameReleaseTarget config depth target)) := by
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let cellWord := AllocationSupport.word config.allocatorCell
  let currentWord := EvmYul.UInt256.ofNat (baseAt config (depth + 1))
  let priorWord := EvmYul.UInt256.ofNat (baseAt config depth)
  let afterBytes := StateRel.pushTargetBy 33 bytesWord target
  let afterCell := StateRel.pushTargetBy 33 cellWord afterBytes
  let afterLoad :=
    StateRel.contractTargetBy 1 currentWord
      (bytesWord :: target.evm.stack) afterCell
  let afterSub :=
    StateRel.contractTargetBy 1 priorWord target.evm.stack afterLoad
  let afterCellStore := StateRel.pushTargetBy 33 cellWord afterSub
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hPriorWord : EvmYul.UInt256.sub currentWord bytesWord = priorWord := by
    change
      EvmYul.UInt256.sub
          (EvmYul.UInt256.ofNat (baseAt config (depth + 1)))
          (EvmYul.UInt256.ofNat
            (MemoryContract.wordBytes * config.frameWords)) =
        EvmYul.UInt256.ofNat (baseAt config depth)
    rw [baseAt_succ]
    exact Assembly.UInt256_ofNat_add_sub_right
      (baseAt config depth) (bytes config)
      (noWrap_of_budget_of_scratchFrameConfig? hConfig hBudget)
  have hAfterCellStack :
      afterCell.evm.stack = cellWord :: bytesWord :: target.evm.stack := rfl
  have hLoad :
      afterCell.evm.toMachineState.mload cellWord =
        (currentWord, afterCell.evm.toMachineState) := by
    have hBaseLoad :=
      Compiler.MemoryRelation.mload_eq_lookup_of_end_le
        target.evm.toMachineState config.allocatorCell hCellAddress
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
    rw [hReady.allocatorAt] at hBaseLoad
    simpa [afterCell, afterBytes, cellWord, currentWord,
      AllocationSupport.word, StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hBaseLoad
  have hAfterLoadStack :
      afterLoad.evm.stack =
        currentWord :: bytesWord :: target.evm.stack := rfl
  have hAfterCellStoreStack :
      afterCellStore.evm.stack =
        cellWord :: priorWord :: target.evm.stack := rfl
  simp only [AllocationSupport.scratchFrameReleaseCode]
  calc
    Structured.InteractionSemantics.Code.openRun
        [.push bytesWord, .push cellWord, .op .mload, .op .sub,
          .push cellWord, .op .mstore] target =
      Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.push bytesWord] target)
        (Structured.InteractionSemantics.Code.openRun
          [.push cellWord, .op .mload, .op .sub,
            .push cellWord, .op .mstore]) := by
      simpa using Structured.InteractionSemantics.Code.openRun_append
        [.push bytesWord]
        [.push cellWord, .op .mload, .op .sub,
          .push cellWord, .op .mstore] target
    _ = Structured.InteractionSemantics.Code.openRun
        [.push cellWord, .op .mload, .op .sub,
          .push cellWord, .op .mstore] afterBytes := by
      rw [Code.openRun_push bytesWord target]
      rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.push cellWord]
          afterBytes)
        (Structured.InteractionSemantics.Code.openRun
          [.op .mload, .op .sub, .push cellWord, .op .mstore]) := by
      simpa using Structured.InteractionSemantics.Code.openRun_append
        [.push cellWord] [.op .mload, .op .sub, .push cellWord, .op .mstore]
        afterBytes
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .mload, .op .sub, .push cellWord, .op .mstore] afterCell := by
      rw [Code.openRun_push cellWord afterBytes]
      rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.op .mload] afterCell)
        (Structured.InteractionSemantics.Code.openRun
          [.op .sub, .push cellWord, .op .mstore]) := by
      simpa using Structured.InteractionSemantics.Code.openRun_append
        [.op .mload] [.op .sub, .push cellWord, .op .mstore] afterCell
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .sub, .push cellWord, .op .mstore] afterLoad := by
      rw [Code.openRun_mload hAfterCellStack hLoad]
      rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.op .sub] afterLoad)
        (Structured.InteractionSemantics.Code.openRun
          [.push cellWord, .op .mstore]) := by
      simpa using Structured.InteractionSemantics.Code.openRun_append
        [.op .sub] [.push cellWord, .op .mstore] afterLoad
    _ = Structured.InteractionSemantics.Code.openRun
        [.push cellWord, .op .mstore] afterSub := by
      rw [Code.openRun_sub hAfterLoadStack, hPriorWord]
      rfl
    _ = Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun [.push cellWord]
          afterSub)
        (Structured.InteractionSemantics.Code.openRun [.op .mstore]) := by
      simpa using Structured.InteractionSemantics.Code.openRun_append
        [.push cellWord] [.op .mstore] afterSub
    _ = Structured.InteractionSemantics.Code.openRun
        [.op .mstore] afterCellStore := by
      rw [Code.openRun_push cellWord afterSub]
      rfl
    _ = .done (.ok (scratchFrameReleaseTarget config depth target)) := by
      simpa [scratchFrameReleaseTarget, bytesWord, cellWord,
        currentWord, priorWord, afterBytes, afterCell, afterLoad,
        afterSub, afterCellStore] using
        Code.openRun_mstore hAfterCellStoreStack

end AllocationInteractionFrameExecution
end Functions
end EvmCompiler
