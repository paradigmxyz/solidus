import EvmCompiler.Functions.AllocationInteractionFrameExecution

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionFramePreservation

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionFrameExecution

@[simp] theorem allocatorAdvanceTarget_stack
    (config : Config) (depth : Nat) (target : TargetState) :
    (allocatorAdvanceTarget config depth target).evm.stack =
      EvmYul.UInt256.ofNat (baseAt config depth) :: target.evm.stack := by
  rfl

theorem allocatorAdvanceTarget_machine
    (config : Config) (depth : Nat) (target : TargetState) :
    (allocatorAdvanceTarget config depth target).evm.toMachineState =
      target.evm.toMachineState.mstore
        (AllocationSupport.word config.allocatorCell)
        (EvmYul.UInt256.ofNat (baseAt config (depth + 1))) := by
  have hNextWord :
      EvmYul.UInt256.add
          (AllocationSupport.frameBytes config.frameWords)
          (EvmYul.UInt256.ofNat (baseAt config depth)) =
        EvmYul.UInt256.ofNat (baseAt config (depth + 1)) := by
    change
      EvmYul.UInt256.ofNat
            (MemoryContract.wordBytes * config.frameWords) +
          EvmYul.UInt256.ofNat (baseAt config depth) =
        EvmYul.UInt256.ofNat (baseAt config (depth + 1))
    rw [Assembly.UInt256_ofNat_add]
    rw [baseAt_succ]
    simp [bytes, Nat.add_comm]
  simp [allocatorAdvanceTarget, hNextWord,
    StateRel.pushTargetBy, StateRel.pushTarget,
    StateRel.contractTargetBy, StateRel.mstoreTarget,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem allocatorAdvanceTarget_machineRel
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config} {sourceMachine : EvmYul.MachineState}
    {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.evm.toMachineState) :
    Compiler.MemoryRelation.MachineRel contract sourceMachine
      (allocatorAdvanceTarget config depth target).evm.toMachineState := by
  obtain
    ⟨reservation, hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
      reservation.containsRegion config.allocatorCell 1 := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.containsRegion
      MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    constructor
    · exact Nat.le_refl _
    · omega
  have hCellEnd :
      config.allocatorCell + MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    lt_of_le_of_lt hRegion.2 hWF.2
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  rw [allocatorAdvanceTarget_machine]
  exact Compiler.MemoryRelation.MachineRel.mstore_target
    config.allocatorCell
    (EvmYul.UInt256.ofNat (baseAt config (depth + 1)))
    hMachine hReservation hRegion hCellEnd hCellHost

theorem allocatorAdvanceTarget_activeWords
    {config : Config} {depth : Nat} {target : TargetState}
    (hReady : AllocatorReady config depth target) :
    (allocatorAdvanceTarget config depth target).evm.activeWords =
      target.evm.activeWords := by
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  rw [allocatorAdvanceTarget_machine]
  simpa [AllocationSupport.word] using
    (Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat (baseAt config (depth + 1)))
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive))

theorem allocatorAdvanceTarget_memorySize
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady : AllocatorReady config depth target) :
    (allocatorAdvanceTarget config depth target).evm.toMachineState.memory.size =
      target.evm.toMachineState.memory.size := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
      reservation.containsRegion config.allocatorCell 1 := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.containsRegion
      MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    constructor
    · exact Nat.le_refl _
    · omega
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  rw [allocatorAdvanceTarget_machine]
  simpa [AllocationSupport.word, EvmYul.MachineState.mstore] using
    (Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat (baseAt config (depth + 1)))
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated))

theorem allocatorAdvanceTarget_ready
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady : AllocatorReady config depth target) :
    AllocatorReady config (depth + 1)
      (allocatorAdvanceTarget config depth target) := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
      reservation.containsRegion config.allocatorCell 1 := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.containsRegion
      MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    constructor
    · exact Nat.le_refl _
    · omega
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  refine
    { allocatorAt := ?_
      cellActive := ?_
      cellAllocated := ?_
      activeNoWrap := ?_ }
  · have hLookup :=
      Compiler.MemoryRelation.lookupMemory_mstore_same
        target.evm.toMachineState config.allocatorCell
        (EvmYul.UInt256.ofNat (baseAt config (depth + 1)))
        hCellAddress
        (by simpa [MemoryContract.wordBytes] using hCellHost)
        (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
    simpa [AllocatorAt, allocatorAdvanceTarget_machine,
      AllocationSupport.word] using hLookup
  · simpa [allocatorAdvanceTarget_activeWords hReady] using hReady.cellActive
  · simpa [allocatorAdvanceTarget_memorySize hConfig hReady] using
      hReady.cellAllocated
  · simpa [allocatorAdvanceTarget_activeWords hReady] using hReady.activeNoWrap

theorem allocatorAdvanceTarget_growth
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady : AllocatorReady config depth target) :
    TargetGrowth target (allocatorAdvanceTarget config depth target) := by
  exact
    ⟨by simp [allocatorAdvanceTarget_activeWords hReady],
      by simp [allocatorAdvanceTarget_memorySize hConfig hReady]⟩

theorem allocatorAdvanceTarget_lookupMemory
    {contract : MemoryContract.Contract}
    {frameWords depth query : Nat} {config : Config}
    {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady : AllocatorReady config depth target)
    (hAfterCell :
      config.allocatorCell + MemoryContract.wordBytes ≤ query)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.evm.activeWords.toNat * MemoryContract.wordBytes) :
    (allocatorAdvanceTarget config depth target).evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) =
      target.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
      reservation.containsRegion config.allocatorCell 1 := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.containsRegion
      MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    constructor
    · exact Nat.le_refl _
    · omega
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hQueryLt : query < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hReady.activeNoWrap)
  have hQuery : (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  rw [allocatorAdvanceTarget_machine]
  simpa [AllocationSupport.word] using
    (Compiler.MemoryRelation.lookupMemory_mstore_disjoint
      target.evm.toMachineState config.allocatorCell query
      (EvmYul.UInt256.ofNat (baseAt config (depth + 1)))
      hCellAddress hQuery
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
      (by simpa [MemoryContract.wordBytes] using hReadMemory)
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
      (Or.inr (by simpa [MemoryContract.wordBytes] using hAfterCell)))

theorem allocatorAdvanceTarget_protectedPrefix
    {contract : MemoryContract.Contract}
    {frameWords depth protectedDepth : Nat} {config : Config}
    {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady : AllocatorReady config depth target) :
    ProtectedPrefix config protectedDepth target
      (allocatorAdvanceTarget config depth target) := by
  obtain
    ⟨_reservation, _hReservation, hAllocator, hFirst, _hLimit,
      _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellBeforeFirst :
      config.allocatorCell + MemoryContract.wordBytes ≤ config.firstFrame := by
    rw [hAllocator, hFirst]
    unfold MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.frameBase
    omega
  refine
    { growth := allocatorAdvanceTarget_growth hConfig hReady
      lookup := ?_ }
  intro address hStart _hEnd hReadMemory hReadActive
  exact allocatorAdvanceTarget_lookupMemory hConfig hReady
    (hCellBeforeFirst.trans hStart) hReadMemory hReadActive

theorem allocatorAdvanceTarget_boundedEffect
    {contract : MemoryContract.Contract}
    {frameWords depth protectedBound : Nat} {config : Config}
    {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady : AllocatorReady config depth target) :
    BoundedEffect config (depth + 1) protectedBound target
      (allocatorAdvanceTarget config depth target) := by
  exact
    { ready := allocatorAdvanceTarget_ready hConfig hReady
      growth := allocatorAdvanceTarget_growth hConfig hReady
      prefixStable := fun _hDepth _hBudget =>
        allocatorAdvanceTarget_protectedPrefix hConfig hReady }

theorem framePreallocTarget_machine_of_words
    {config : Config} {frameDepth slot : Nat} {rest : List Word}
    {target : TargetState}
    (hWords : config.frameWords = slot + 1)
    (hAddress :
      EvmYul.UInt256.add
          (AllocationSupport.slotOffset slot)
          (EvmYul.UInt256.ofNat (baseAt config frameDepth)) =
        EvmYul.UInt256.ofNat
          (scratchAddress (baseAt config frameDepth) slot)) :
    (framePreallocTarget config frameDepth rest target).evm.toMachineState =
      target.evm.toMachineState.mstore
        (EvmYul.UInt256.ofNat
          (scratchAddress (baseAt config frameDepth) slot))
        AllocationSupport.zeroWord := by
  simp [framePreallocTarget, hWords, hAddress,
    StateRel.pushTargetBy, StateRel.pushTarget,
    StateRel.contractTargetBy, StateRel.mstoreTarget,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem framePrealloc_last_address_facts
    {contract : MemoryContract.Contract}
    {frameWords frameDepth slot : Nat} {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config frameDepth)
    (hWords : config.frameWords = slot + 1) :
    let frameBase := baseAt config frameDepth
    let address := scratchAddress frameBase slot
    address + MemoryContract.wordBytes < EvmYul.UInt256.size ∧
      address + MemoryContract.wordBytes < USize.size ∧
      (EvmYul.UInt256.ofNat address).toNat = address ∧
      EvmYul.UInt256.add
          (AllocationSupport.slotOffset slot)
          (EvmYul.UInt256.ofNat frameBase) =
        EvmYul.UInt256.ofNat address := by
  let frameBase := baseAt config frameDepth
  let address := scratchAddress frameBase slot
  have hFrameEnd :
      address + MemoryContract.wordBytes =
        frameBase + bytes config := by
    simp [address, frameBase, scratchAddress, bytes, hWords,
      MemoryContract.wordBytes, Nat.mul_add, Nat.add_assoc]
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size := by
    rw [hFrameEnd]
    exact noWrap_of_budget_of_scratchFrameConfig? hConfig hBudget
  have hAddressHost :
      address + MemoryContract.wordBytes < USize.size := by
    rw [hFrameEnd]
    exact hostAddressable_of_budget_of_scratchFrameConfig? hConfig hBudget
  have hAddressLt : address < EvmYul.UInt256.size := by omega
  refine
    ⟨hAddressEnd, hAddressHost,
      EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt, ?_⟩
  change
    EvmYul.UInt256.ofNat (32 * slot) +
        EvmYul.UInt256.ofNat frameBase =
      EvmYul.UInt256.ofNat
        (frameBase + MemoryContract.wordBytes * slot)
  rw [Assembly.UInt256_ofNat_add]
  simp [MemoryContract.wordBytes, Nat.add_comm]

theorem framePreallocTarget_growth
    {contract : MemoryContract.Contract}
    {frameWords frameDepth : Nat} {config : Config}
    {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth) :
    TargetGrowth target
      (framePreallocTarget config frameDepth rest target) := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨hAddressEnd, hAddressHost, hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      have hMachine :=
        framePreallocTarget_machine_of_words
          (target := target) (rest := rest) hWords hAddress
      refine ⟨?_, ?_⟩
      · rw [hMachine]
        exact
          Compiler.MemoryRelation.activeWords_toNat_le_mstore
            target.evm.toMachineState
            (scratchAddress (baseAt config frameDepth) slot)
            AllocationSupport.zeroWord hAddressEnd
      · rw [hMachine]
        simpa [EvmYul.MachineState.mstore] using
          (Compiler.MemoryRelation.writeWord_memory_size_ge
            target.evm.toMachineState
            (scratchAddress (baseAt config frameDepth) slot)
            AllocationSupport.zeroWord hAddressToNat
            (by simpa [MemoryContract.wordBytes] using hAddressHost))

theorem framePreallocTarget_lookupMemory
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth query : Nat}
    {config : Config} {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth)
    (hReady : AllocatorReady config allocatorDepth target)
    (hBeforeFrame :
      query + MemoryContract.wordBytes ≤ baseAt config frameDepth)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.evm.activeWords.toNat * MemoryContract.wordBytes) :
    (framePreallocTarget config frameDepth rest target).evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) =
      target.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨_hAddressEnd, hAddressHost, hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      have hQueryLt : query < EvmYul.UInt256.size :=
        lt_of_le_of_lt
          (Nat.le_add_right query MemoryContract.wordBytes)
          (hReadActive.trans_lt hReady.activeNoWrap)
      have hQuery : (EvmYul.UInt256.ofNat query).toNat = query :=
        EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
      rw [framePreallocTarget_machine_of_words hWords hAddress]
      exact
        Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
          target.evm.toMachineState
          (scratchAddress (baseAt config frameDepth) slot)
          query AllocationSupport.zeroWord hAddressToNat hQuery
          (by simpa [MemoryContract.wordBytes] using hAddressHost)
          (by simpa [MemoryContract.wordBytes] using hReadMemory)
          (by simpa [MemoryContract.wordBytes] using hReadActive)
          (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
          (Or.inl
            (hBeforeFrame.trans
              (Nat.le_add_right (baseAt config frameDepth)
                (MemoryContract.wordBytes * slot))))

theorem framePreallocTarget_machineRel
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth : Nat}
    {config : Config} {sourceMachine : EvmYul.MachineState}
    {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.evm.toMachineState) :
    Compiler.MemoryRelation.MachineRel contract sourceMachine
      (framePreallocTarget config frameDepth rest target).evm.toMachineState := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨hAddressEnd, hAddressHost, _hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      obtain
        ⟨reservation, hReservation, _hAllocator, hFirst, hLimit,
          _hConfigWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hConfig
      have hBaseLower :
          config.firstFrame ≤ baseAt config frameDepth := by
        simpa using baseAt_mono config (Nat.zero_le frameDepth)
      have hRegion :
          reservation.containsRegion
            (scratchAddress (baseAt config frameDepth) slot) 1 := by
        constructor
        · have hReservationBase : reservation.base ≤ config.firstFrame := by
            rw [hFirst]
            unfold MemoryContract.ScratchReservation.frameBase
            omega
          exact hReservationBase.trans
            (hBaseLower.trans
              (Nat.le_add_right (baseAt config frameDepth)
                (MemoryContract.wordBytes * slot)))
        · have hFrameEnd :
              scratchAddress (baseAt config frameDepth) slot +
                    MemoryContract.wordBytes =
                baseAt config frameDepth + bytes config := by
            simp [scratchAddress, bytes, hWords, MemoryContract.wordBytes,
              Nat.mul_add, Nat.add_assoc]
          change
            scratchAddress (baseAt config frameDepth) slot +
                MemoryContract.wordBytes ≤ reservation.endExclusive
          rw [hFrameEnd, ← hLimit]
          exact hBudget
      rw [framePreallocTarget_machine_of_words hWords hAddress]
      exact Compiler.MemoryRelation.MachineRel.mstore_target
        (scratchAddress (baseAt config frameDepth) slot)
        AllocationSupport.zeroWord hMachine hReservation hRegion
        hAddressEnd hAddressHost

theorem framePreallocTarget_ready
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth : Nat}
    {config : Config} {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth)
    (hReady : AllocatorReady config allocatorDepth target) :
    AllocatorReady config allocatorDepth
      (framePreallocTarget config frameDepth rest target) := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨hAddressEnd, hAddressHost, hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      obtain
        ⟨_reservation, _hReservation, hAllocator, hFirst, _hLimit,
          _hConfigWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hConfig
      have hBaseLower :
          config.firstFrame ≤ baseAt config frameDepth := by
        simpa using baseAt_mono config (Nat.zero_le frameDepth)
      have hCellBeforeAddress :
          config.allocatorCell + MemoryContract.wordBytes ≤
            scratchAddress (baseAt config frameDepth) slot := by
        have hCellBeforeFrame :
            config.allocatorCell + MemoryContract.wordBytes ≤
              baseAt config frameDepth := by
          rw [hAllocator]
          rw [hFirst] at hBaseLower
          unfold MemoryContract.ScratchReservation.allocatorCell
          unfold MemoryContract.ScratchReservation.frameBase at hBaseLower
          simpa using hBaseLower
        exact hCellBeforeFrame.trans
          (Nat.le_add_right (baseAt config frameDepth)
            (MemoryContract.wordBytes * slot))
      have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
        lt_of_le_of_lt
          (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
          (hReady.cellActive.trans_lt hReady.activeNoWrap)
      have hCellAddress :
          (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
            config.allocatorCell :=
        EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
      have hLookup :=
        Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
          target.evm.toMachineState
          (scratchAddress (baseAt config frameDepth) slot)
          config.allocatorCell AllocationSupport.zeroWord
          hAddressToNat hCellAddress
          (by simpa [MemoryContract.wordBytes] using hAddressHost)
          (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
          (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
          (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
          (Or.inl
            (by simpa [MemoryContract.wordBytes] using hCellBeforeAddress))
      have hAllocatorPreserved :
          AllocatorAt config allocatorDepth
            (framePreallocTarget config frameDepth rest target) := by
        rw [hReady.allocatorAt] at hLookup
        simpa [AllocatorAt,
          framePreallocTarget_machine_of_words hWords hAddress] using hLookup
      have hActiveMono :=
        Compiler.MemoryRelation.activeWords_toNat_le_mstore
          target.evm.toMachineState
          (scratchAddress (baseAt config frameDepth) slot)
          AllocationSupport.zeroWord hAddressEnd
      have hMemoryMono :=
        Compiler.MemoryRelation.writeWord_memory_size_ge
          target.evm.toMachineState
          (scratchAddress (baseAt config frameDepth) slot)
          AllocationSupport.zeroWord hAddressToNat
          (by simpa [MemoryContract.wordBytes] using hAddressHost)
      refine
        { allocatorAt := hAllocatorPreserved
          cellActive := ?_
          cellAllocated := ?_
          activeNoWrap := ?_ }
      · have hScaled :
            target.evm.activeWords.toNat * MemoryContract.wordBytes ≤
              (target.evm.toMachineState.mstore
                (EvmYul.UInt256.ofNat
                  (scratchAddress (baseAt config frameDepth) slot))
                AllocationSupport.zeroWord).activeWords.toNat *
                MemoryContract.wordBytes :=
          Nat.mul_le_mul_right MemoryContract.wordBytes hActiveMono
        simpa [framePreallocTarget_machine_of_words hWords hAddress] using
          hReady.cellActive.trans hScaled
      · simpa [framePreallocTarget_machine_of_words hWords hAddress,
          EvmYul.MachineState.mstore] using
          hReady.cellAllocated.trans hMemoryMono
      · simpa [framePreallocTarget_machine_of_words hWords hAddress,
          MemoryContract.wordBytes] using
          (Compiler.MemoryRelation.mstore_activeBytes_lt_size_of_activeBytes_lt_size
            target.evm.toMachineState
            (scratchAddress (baseAt config frameDepth) slot)
            AllocationSupport.zeroWord
            (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
            (by simpa [MemoryContract.wordBytes] using hAddressHost))

@[simp] theorem framePreallocTarget_stack
    {config : Config} {frameDepth : Nat} {rest : List Word}
    {target : TargetState}
    (hPositive : 0 < config.frameWords)
    (hStack :
      target.evm.stack =
        EvmYul.UInt256.ofNat (baseAt config frameDepth) :: rest) :
    (framePreallocTarget config frameDepth rest target).evm.stack =
      EvmYul.UInt256.ofNat (baseAt config frameDepth) :: rest := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      simp [framePreallocTarget, hWords, StateRel.pushTargetBy,
        StateRel.pushTarget, StateRel.contractTargetBy,
        StateRel.mstoreTarget, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem framePreallocTarget_frameActive
    {contract : MemoryContract.Contract}
    {frameWords frameDepth : Nat} {config : Config}
    {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth) :
    baseAt config frameDepth + bytes config ≤
      (framePreallocTarget config frameDepth rest target).evm.activeWords.toNat *
        MemoryContract.wordBytes := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨hAddressEnd, _hAddressHost, _hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      have hFrameEnd :
          scratchAddress (baseAt config frameDepth) slot +
                MemoryContract.wordBytes =
            baseAt config frameDepth + bytes config := by
        simp [scratchAddress, bytes, hWords, MemoryContract.wordBytes,
          Nat.mul_add, Nat.add_assoc]
      rw [← hFrameEnd]
      rw [framePreallocTarget_machine_of_words hWords hAddress]
      simpa [MemoryContract.wordBytes] using
        (Compiler.MemoryRelation.mstore_end_le_activeBytes
          target.evm.toMachineState
          (scratchAddress (baseAt config frameDepth) slot)
          AllocationSupport.zeroWord
          (by simpa [MemoryContract.wordBytes] using hAddressEnd))

theorem framePreallocTarget_frameAllocated
    {contract : MemoryContract.Contract}
    {frameWords frameDepth : Nat} {config : Config}
    {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth) :
    baseAt config frameDepth + bytes config ≤
      (framePreallocTarget config frameDepth rest target).evm.toMachineState.memory.size := by
  cases hWords : config.frameWords with
  | zero => simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨_hAddressEnd, hAddressHost, hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      have hFrameEnd :
          scratchAddress (baseAt config frameDepth) slot +
                MemoryContract.wordBytes =
            baseAt config frameDepth + bytes config := by
        simp [scratchAddress, bytes, hWords, MemoryContract.wordBytes,
          Nat.mul_add, Nat.add_assoc]
      rw [← hFrameEnd]
      rw [framePreallocTarget_machine_of_words hWords hAddress]
      simpa [EvmYul.MachineState.mstore] using
        (Compiler.MemoryRelation.writeWord_memory_size_ge_end
          target.evm.toMachineState
          (scratchAddress (baseAt config frameDepth) slot)
          AllocationSupport.zeroWord hAddressToNat
          (by simpa [MemoryContract.wordBytes] using hAddressHost))

theorem framePreallocTarget_protectedPrefix
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth protectedDepth : Nat}
    {config : Config} {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth)
    (hReady : AllocatorReady config allocatorDepth target)
    (hProtected : protectedDepth ≤ frameDepth) :
    ProtectedPrefix config protectedDepth target
      (framePreallocTarget config frameDepth rest target) := by
  refine
    { growth := framePreallocTarget_growth hConfig hPositive hBudget
      lookup := ?_ }
  intro address _hStart hEnd hReadMemory hReadActive
  exact framePreallocTarget_lookupMemory hConfig hPositive hBudget hReady
    (hEnd.trans (baseAt_mono config hProtected))
    hReadMemory hReadActive

theorem framePreallocTarget_boundedEffect
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth protectedBound : Nat}
    {config : Config} {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config frameDepth)
    (hReady : AllocatorReady config allocatorDepth target)
    (hBound : protectedBound ≤ frameDepth + 1) :
    BoundedEffect config allocatorDepth protectedBound target
      (framePreallocTarget config frameDepth rest target) := by
  exact
    { ready := framePreallocTarget_ready hConfig hPositive hBudget hReady
      growth := framePreallocTarget_growth hConfig hPositive hBudget
      prefixStable := fun hDepth _hProtectedBudget =>
        framePreallocTarget_protectedPrefix hConfig hPositive hBudget hReady
          (by omega) }

/-- Checked resource behavior of the ordinary emitted frame-acquire sequence. -/
structure ScratchFrameAcquireCorrect
    (contract : MemoryContract.Contract) (config : Config) (depth : Nat)
    (sourceMachine : EvmYul.MachineState)
    (before after : TargetState) : Prop where
  execution :
    Structured.InteractionSemantics.Code.openRun
        (AllocationSupport.scratchFrameAcquireCode config) before =
      .done (.ok after)
  stack :
    after.evm.stack =
      EvmYul.UInt256.ofNat (baseAt config depth) :: before.evm.stack
  machine :
    Compiler.MemoryRelation.MachineRel contract sourceMachine
      after.evm.toMachineState
  effect : BoundedEffect config (depth + 1) (depth + 1) before after
  frameActive :
    baseAt config depth + bytes config ≤
      after.evm.activeWords.toNat * MemoryContract.wordBytes
  frameAllocated :
    baseAt config depth + bytes config ≤
      after.evm.toMachineState.memory.size

theorem scratchFrameAcquire_correct
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config} {sourceMachine : EvmYul.MachineState}
    {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config depth)
    (hReady : AllocatorReady config depth target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.evm.toMachineState) :
    ScratchFrameAcquireCorrect contract config depth sourceMachine target
      (scratchFrameAcquireTarget config depth target) := by
  let advanced := allocatorAdvanceTarget config depth target
  have hAdvanceReady : AllocatorReady config (depth + 1) advanced := by
    simpa [advanced] using allocatorAdvanceTarget_ready hConfig hReady
  have hAdvanceMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        advanced.evm.toMachineState := by
    simpa [advanced] using
      allocatorAdvanceTarget_machineRel (depth := depth) hConfig hMachine
  have hAdvanceStack :
      advanced.evm.stack =
        EvmYul.UInt256.ofNat (baseAt config depth) :: target.evm.stack := by
    simp [advanced]
  have hAdvanceEffect :
      BoundedEffect config (depth + 1) (depth + 1) target advanced := by
    simpa [advanced] using
      allocatorAdvanceTarget_boundedEffect
        (protectedBound := depth + 1) hConfig hReady
  have hPreallocEffect :
      BoundedEffect config (depth + 1) (depth + 1) advanced
        (framePreallocTarget config depth target.evm.stack advanced) := by
    exact framePreallocTarget_boundedEffect hConfig hPositive hBudget
      hAdvanceReady (by omega)
  refine
    { execution := scratchFrameAcquire_openRun hPositive hReady
      stack := ?_
      machine := ?_
      effect := ?_
      frameActive := ?_
      frameAllocated := ?_ }
  · simpa [scratchFrameAcquireTarget, advanced] using
      framePreallocTarget_stack hPositive hAdvanceStack
  · simpa [scratchFrameAcquireTarget, advanced] using
      framePreallocTarget_machineRel
        (allocatorDepth := depth + 1) hConfig hPositive hBudget
        hAdvanceMachine
  · simpa [scratchFrameAcquireTarget, advanced] using
      hAdvanceEffect.trans hPreallocEffect
  · simpa [scratchFrameAcquireTarget, advanced] using
      framePreallocTarget_frameActive
        (target := advanced) (rest := target.evm.stack)
        hConfig hPositive hBudget
  · simpa [scratchFrameAcquireTarget, advanced] using
      framePreallocTarget_frameAllocated
        (target := advanced) (rest := target.evm.stack)
        hConfig hPositive hBudget

end AllocationInteractionFramePreservation
end Functions
end EvmCompiler
