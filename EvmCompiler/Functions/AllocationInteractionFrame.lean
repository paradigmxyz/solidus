import EvmCompiler.Functions.AllocationInteractionRelation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionFrame

open AllocationInteractionRelation

abbrev Config := AllocationSupport.ScratchFrameConfig

def bytes (config : Config) : Nat :=
  MemoryContract.wordBytes * config.frameWords

def baseAt (config : Config) (depth : Nat) : Nat :=
  config.firstFrame + depth * bytes config

def Budget (config : Config) (depth : Nat) : Prop :=
  baseAt config depth + bytes config ≤ config.limit

namespace Budget

/-- A budget for a deeper allocator position also covers every shallower one. -/
theorem mono {config : Config} {smaller larger : Nat}
    (hDepth : smaller ≤ larger) (hBudget : Budget config larger) :
    Budget config smaller := by
  unfold Budget baseAt at hBudget ⊢
  have hScaled := Nat.mul_le_mul_right (bytes config) hDepth
  omega

end Budget

def AllocatorAt (config : Config) (depth : Nat)
    (target : TargetState) : Prop :=
  target.evm.toMachineState.lookupMemory
      (EvmYul.UInt256.ofNat config.allocatorCell) =
    EvmYul.UInt256.ofNat (baseAt config depth)

/-- Target execution grows, but never shrinks, machine memory. -/
structure TargetGrowth (before after : TargetState) : Prop where
  active : before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat
  memory :
    before.evm.toMachineState.memory.size ≤
      after.evm.toMachineState.memory.size

namespace TargetGrowth

theorem refl (target : TargetState) : TargetGrowth target target :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem trans {first second third : TargetState}
    (hFirst : TargetGrowth first second)
    (hSecond : TargetGrowth second third) :
    TargetGrowth first third :=
  ⟨hFirst.active.trans hSecond.active,
    hFirst.memory.trans hSecond.memory⟩

end TargetGrowth

/-- The scratch allocator cell is materialized at one exact frame depth. -/
structure AllocatorReady (config : Config) (depth : Nat)
    (target : TargetState) : Prop where
  allocatorAt : AllocatorAt config depth target
  cellActive :
    config.allocatorCell + MemoryContract.wordBytes ≤
      target.evm.activeWords.toNat * MemoryContract.wordBytes
  cellAllocated :
    config.allocatorCell + MemoryContract.wordBytes ≤
      target.evm.toMachineState.memory.size
  activeNoWrap :
    target.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

/-- A transition leaves every already-live suspended-frame word unchanged. -/
structure ProtectedPrefix (config : Config) (depth : Nat)
    (before after : TargetState) : Prop where
  growth : TargetGrowth before after
  lookup :
    ∀ {address : Nat},
      config.firstFrame ≤ address →
      address + MemoryContract.wordBytes ≤ baseAt config depth →
      address + MemoryContract.wordBytes ≤
        before.evm.toMachineState.memory.size →
      address + MemoryContract.wordBytes ≤
        before.evm.activeWords.toNat * MemoryContract.wordBytes →
      after.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat address) =
        before.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat address)

namespace ProtectedPrefix

theorem refl (config : Config) (depth : Nat) (target : TargetState) :
    ProtectedPrefix config depth target target :=
  ⟨TargetGrowth.refl target, by intros; rfl⟩

theorem trans {config : Config} {depth : Nat}
    {first second third : TargetState}
    (hFirst : ProtectedPrefix config depth first second)
    (hSecond : ProtectedPrefix config depth second third) :
    ProtectedPrefix config depth first third := by
  refine ⟨hFirst.growth.trans hSecond.growth, ?_⟩
  intro address hStart hEnd hMemory hActive
  exact
    (hSecond.lookup hStart hEnd
      (hMemory.trans hFirst.growth.memory)
      (hActive.trans
        (Nat.mul_le_mul_right MemoryContract.wordBytes
          hFirst.growth.active))).trans
      (hFirst.lookup hStart hEnd hMemory hActive)

theorem of_machine_eq {config : Config} {depth : Nat}
    {before after : TargetState}
    (hMachine :
      after.evm.toMachineState = before.evm.toMachineState) :
    ProtectedPrefix config depth before after := by
  exact
    { growth :=
        { active := by simpa [hMachine]
          memory := by simpa [hMachine] }
      lookup := by
        intro address _hStart _hEnd _hMemory _hActive
        change
          after.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat address) =
            before.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat address)
        rw [hMachine] }

theorem of_memory_eq_active_growth {config : Config} {depth : Nat}
    {before after : TargetState}
    (hMemory :
      after.evm.toMachineState.memory = before.evm.toMachineState.memory)
    (hActive :
      before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat)
    (hBeforeNoWrap :
      before.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hAfterNoWrap :
      after.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    ProtectedPrefix config depth before after := by
  refine
    { growth :=
        { active := hActive
          memory := by simpa [hMemory] }
      lookup := ?_ }
  intro address _hStart _hEnd hReadMemory hReadActive
  have hAddressLt : address < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right address MemoryContract.wordBytes)
      (hReadActive.trans_lt hBeforeNoWrap)
  exact
    Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
      address (EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt)
      hMemory hActive hBeforeNoWrap hAfterNoWrap hReadMemory hReadActive

end ProtectedPrefix

namespace AllocatorReady

theorem of_lookup_growth {config : Config} {depth : Nat}
    {before after : TargetState}
    (hReady : AllocatorReady config depth before)
    (hLookup :
      after.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat config.allocatorCell) =
        before.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat config.allocatorCell))
    (hActive :
      before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat)
    (hMemory :
      before.evm.toMachineState.memory.size ≤
        after.evm.toMachineState.memory.size)
    (hNoWrap :
      after.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorReady config depth after := by
  exact
    { allocatorAt := hLookup.trans hReady.allocatorAt
      cellActive := hReady.cellActive.trans
        (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
      cellAllocated := hReady.cellAllocated.trans hMemory
      activeNoWrap := hNoWrap }

theorem of_memory_eq_active_growth {config : Config} {depth : Nat}
    {before after : TargetState}
    (hReady : AllocatorReady config depth before)
    (hMemory :
      after.evm.toMachineState.memory = before.evm.toMachineState.memory)
    (hActive :
      before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat)
    (hNoWrap :
      after.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorReady config depth after := by
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellWord :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hLookup :=
    Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
      config.allocatorCell hCellWord hMemory hActive
      hReady.activeNoWrap hNoWrap hReady.cellAllocated hReady.cellActive
  exact hReady.of_lookup_growth hLookup hActive
    (by simpa [hMemory]) hNoWrap

theorem of_machine_eq {config : Config} {depth : Nat}
    {before after : TargetState}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.evm.toMachineState = before.evm.toMachineState) :
    AllocatorReady config depth after := by
  exact hReady.of_memory_eq_active_growth
    (by simpa [hMachine]) (by simpa [hMachine])
    (by simpa [hMachine] using hReady.activeNoWrap)

/-- A compiler spill disjoint from the allocator cell preserves readiness. -/
theorem of_mstore_disjoint
    {config : Config} {depth address : Nat} {value : Word}
    {before after : TargetState}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.evm.toMachineState =
        before.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat address) value)
    (hAddress : (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size)
    (hDisjoint :
      config.allocatorCell + MemoryContract.wordBytes ≤ address ∨
        address + MemoryContract.wordBytes ≤ config.allocatorCell) :
    AllocatorReady config depth after := by
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCell :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hLookup :
      after.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat config.allocatorCell) =
        before.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat config.allocatorCell) := by
    rw [hMachine]
    exact
      Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
        before.evm.toMachineState address config.allocatorCell value
        hAddress hCell
        (by simpa [MemoryContract.wordBytes] using hHost)
        (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
        (by simpa [MemoryContract.wordBytes] using hDisjoint)
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size :=
    lt_trans hHost Compiler.MemoryRelation.usize_size_lt_uint256_size
  have hActive :
      before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat := by
    rw [hMachine]
    exact
      Compiler.MemoryRelation.activeWords_toNat_le_mstore
        before.evm.toMachineState address value hAddressEnd
  have hMemory :
      before.evm.toMachineState.memory.size ≤
        after.evm.toMachineState.memory.size := by
    rw [hMachine]
    simpa [EvmYul.MachineState.mstore] using
      (Compiler.MemoryRelation.writeWord_memory_size_ge
        before.evm.toMachineState address value hAddress
        (by simpa [MemoryContract.wordBytes] using hHost))
  have hNoWrap :
      after.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    rw [hMachine]
    simpa [MemoryContract.wordBytes] using
      (Compiler.MemoryRelation.mstore_activeBytes_lt_size_of_activeBytes_lt_size
        before.evm.toMachineState address value
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
        (by simpa [MemoryContract.wordBytes] using hHost))
  exact hReady.of_lookup_growth hLookup hActive hMemory hNoWrap

end AllocatorReady

/-- Ordinary execution at a fixed allocator depth protects that depth too. -/
structure AllocatorEffect (config : Config) (depth : Nat)
    (before after : TargetState) : Prop where
  ready : AllocatorReady config depth after
  growth : TargetGrowth before after
  prefixStable :
    ∀ {protectedDepth : Nat},
      protectedDepth ≤ depth →
      Budget config protectedDepth →
      ProtectedPrefix config protectedDepth before after

namespace AllocatorEffect

theorem refl {config : Config} {depth : Nat} {target : TargetState}
    (hReady : AllocatorReady config depth target) :
    AllocatorEffect config depth target target :=
  { ready := hReady
    growth := TargetGrowth.refl target
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.refl config _ target }

theorem trans {config : Config} {depth : Nat}
    {first second third : TargetState}
    (hFirst : AllocatorEffect config depth first second)
    (hSecond : AllocatorEffect config depth second third) :
    AllocatorEffect config depth first third :=
  { ready := hSecond.ready
    growth := hFirst.growth.trans hSecond.growth
    prefixStable := fun hDepth hBudget =>
      (hFirst.prefixStable hDepth hBudget).trans
        (hSecond.prefixStable hDepth hBudget) }

theorem of_machine_eq {config : Config} {depth : Nat}
    {before after : TargetState}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.evm.toMachineState = before.evm.toMachineState) :
    AllocatorEffect config depth before after :=
  { ready := hReady.of_machine_eq hMachine
    growth :=
      { active := by simpa [hMachine]
        memory := by simpa [hMachine] }
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.of_machine_eq hMachine }

theorem of_memory_eq_active_growth {config : Config} {depth : Nat}
    {before after : TargetState}
    (hReady : AllocatorReady config depth before)
    (hMemory :
      after.evm.toMachineState.memory = before.evm.toMachineState.memory)
    (hActive :
      before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat)
    (hAfterNoWrap :
      after.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorEffect config depth before after :=
  { ready := hReady.of_memory_eq_active_growth
      hMemory hActive hAfterNoWrap
    growth :=
      { active := hActive
        memory := by simpa [hMemory] }
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.of_memory_eq_active_growth
        hMemory hActive hReady.activeNoWrap hAfterNoWrap }

end AllocatorEffect

/-- Statement execution may mutate its own frame, but protects older frames. -/
structure SuspendedEffect (config : Config) (depth : Nat)
    (before after : TargetState) : Prop where
  ready : AllocatorReady config depth after
  growth : TargetGrowth before after
  prefixStable :
    ∀ {protectedDepth : Nat},
      protectedDepth < depth →
      Budget config protectedDepth →
      ProtectedPrefix config protectedDepth before after

namespace SuspendedEffect

theorem of_allocatorEffect {config : Config} {depth : Nat}
    {before after : TargetState}
    (hEffect : AllocatorEffect config depth before after) :
    SuspendedEffect config depth before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := fun hDepth hBudget =>
      hEffect.prefixStable (Nat.le_of_lt hDepth) hBudget }

theorem refl {config : Config} {depth : Nat} {target : TargetState}
    (hReady : AllocatorReady config depth target) :
    SuspendedEffect config depth target target :=
  of_allocatorEffect (AllocatorEffect.refl hReady)

theorem trans {config : Config} {depth : Nat}
    {first second third : TargetState}
    (hFirst : SuspendedEffect config depth first second)
    (hSecond : SuspendedEffect config depth second third) :
    SuspendedEffect config depth first third :=
  { ready := hSecond.ready
    growth := hFirst.growth.trans hSecond.growth
    prefixStable := fun hDepth hBudget =>
      (hFirst.prefixStable hDepth hBudget).trans
        (hSecond.prefixStable hDepth hBudget) }

end SuspendedEffect

/-- Call phases may change depth while preserving one independent prefix. -/
structure BoundedEffect (config : Config)
    (finalDepth protectedBound : Nat)
    (before after : TargetState) : Prop where
  ready : AllocatorReady config finalDepth after
  growth : TargetGrowth before after
  prefixStable :
    ∀ {protectedDepth : Nat},
      protectedDepth < protectedBound →
      Budget config protectedDepth →
      ProtectedPrefix config protectedDepth before after

namespace BoundedEffect

theorem refl {config : Config} {finalDepth protectedBound : Nat}
    {target : TargetState}
    (hReady : AllocatorReady config finalDepth target) :
    BoundedEffect config finalDepth protectedBound target target :=
  { ready := hReady
    growth := TargetGrowth.refl target
    prefixStable := fun _ _ => ProtectedPrefix.refl config _ target }

theorem of_machine_eq {config : Config}
    {finalDepth protectedBound : Nat} {before after : TargetState}
    (hReady : AllocatorReady config finalDepth before)
    (hMachine :
      after.evm.toMachineState = before.evm.toMachineState) :
    BoundedEffect config finalDepth protectedBound before after :=
  { ready := hReady.of_machine_eq hMachine
    growth :=
      { active := by simpa [hMachine]
        memory := by simpa [hMachine] }
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.of_machine_eq hMachine }

theorem trans {config : Config}
    {firstDepth finalDepth protectedBound : Nat}
    {first second third : TargetState}
    (hFirst :
      BoundedEffect config firstDepth protectedBound first second)
    (hSecond :
      BoundedEffect config finalDepth protectedBound second third) :
    BoundedEffect config finalDepth protectedBound first third :=
  { ready := hSecond.ready
    growth := hFirst.growth.trans hSecond.growth
    prefixStable := fun hDepth hBudget =>
      (hFirst.prefixStable hDepth hBudget).trans
        (hSecond.prefixStable hDepth hBudget) }

theorem weaken {config : Config}
    {finalDepth smallerBound largerBound : Nat}
    {before after : TargetState}
    (hBound : smallerBound ≤ largerBound)
    (hEffect :
      BoundedEffect config finalDepth largerBound before after) :
    BoundedEffect config finalDepth smallerBound before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := fun hDepth hBudget =>
      hEffect.prefixStable (hDepth.trans_le hBound) hBudget }

theorem of_allocatorEffect {config : Config} {depth : Nat}
    {before after : TargetState}
    (hEffect : AllocatorEffect config depth before after) :
    BoundedEffect config depth (depth + 1) before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := fun hDepth hBudget =>
      hEffect.prefixStable (by omega) hBudget }

theorem of_suspendedEffect {config : Config} {depth : Nat}
    {before after : TargetState}
    (hEffect : SuspendedEffect config depth before after) :
    BoundedEffect config depth depth before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := hEffect.prefixStable }

/--
One target `MSTORE` above an independently chosen protected prefix preserves
a bounded allocator effect, even when a deeper callee frame remains ready.
-/
theorem of_mstore_above
    {config : Config} {finalDepth protectedBound address : Nat}
    {value : Word} {before after : TargetState}
    (hReady : AllocatorReady config finalDepth before)
    (hMachine :
      after.evm.toMachineState =
        before.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat address) value)
    (hAddress : (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size)
    (hAllocatorDisjoint :
      config.allocatorCell + MemoryContract.wordBytes ≤ address ∨
        address + MemoryContract.wordBytes ≤ config.allocatorCell)
    (hAbove :
      ∀ {protectedDepth : Nat},
        protectedDepth < protectedBound →
        baseAt config protectedDepth ≤ address) :
    BoundedEffect config finalDepth protectedBound before after := by
  have hFinalReady :=
    hReady.of_mstore_disjoint hMachine hAddress hHost hAllocatorDisjoint
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size :=
    lt_trans hHost Compiler.MemoryRelation.usize_size_lt_uint256_size
  have hGrowth : TargetGrowth before after := by
    refine ⟨?_, ?_⟩
    · rw [hMachine]
      exact
        Compiler.MemoryRelation.activeWords_toNat_le_mstore
          before.evm.toMachineState address value hAddressEnd
    · rw [hMachine]
      simpa [EvmYul.MachineState.mstore] using
        (Compiler.MemoryRelation.writeWord_memory_size_ge
          before.evm.toMachineState address value hAddress
          (by simpa [MemoryContract.wordBytes] using hHost))
  refine
    { ready := hFinalReady
      growth := hGrowth
      prefixStable := ?_ }
  intro protectedDepth hDepth _hBudget
  refine { growth := hGrowth, lookup := ?_ }
  intro query _hStart hEnd hReadMemory hReadActive
  have hQueryLt : query < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hReady.activeNoWrap)
  have hQuery : (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  rw [hMachine]
  exact
    Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
      before.evm.toMachineState address query value hAddress hQuery
      (by simpa [MemoryContract.wordBytes] using hHost)
      (by simpa [MemoryContract.wordBytes] using hReadMemory)
      (by simpa [MemoryContract.wordBytes] using hReadActive)
      (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
      (Or.inl (hEnd.trans (hAbove hDepth)))

end BoundedEffect

/--
Statement resource effect selected by the activation representation. Stack
activations protect the current allocator depth; scratch activations may update
their current frame and therefore protect only strictly suspended depths.
-/
def ActivationEffect
    (config : Config) (depth : Nat) (mode : ActivationMode)
    (before after : TargetState) : Prop :=
  match mode with
  | .stack => AllocatorEffect config depth before after
  | .scratch _ _ => SuspendedEffect config depth before after

namespace ActivationEffect

theorem of_allocatorEffect
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState}
    (hEffect : AllocatorEffect config depth before after) :
    ActivationEffect config depth mode before after := by
  cases mode with
  | stack => exact hEffect
  | scratch => exact SuspendedEffect.of_allocatorEffect hEffect

theorem ready
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState}
    (hEffect : ActivationEffect config depth mode before after) :
    AllocatorReady config depth after := by
  cases mode with
  | stack => exact AllocatorEffect.ready hEffect
  | scratch => exact SuspendedEffect.ready hEffect

theorem growth
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState}
    (hEffect : ActivationEffect config depth mode before after) :
    TargetGrowth before after := by
  cases mode with
  | stack => exact AllocatorEffect.growth hEffect
  | scratch => exact SuspendedEffect.growth hEffect

theorem to_suspendedEffect
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState}
    (hEffect : ActivationEffect config depth mode before after) :
    SuspendedEffect config depth before after := by
  cases mode with
  | stack => exact SuspendedEffect.of_allocatorEffect hEffect
  | scratch => exact hEffect

theorem to_boundedEffect
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState}
    (hEffect : ActivationEffect config depth mode before after) :
    BoundedEffect config depth
        (match mode with
        | .stack => depth + 1
        | .scratch _ _ => depth)
        before after := by
  cases mode with
  | stack => exact BoundedEffect.of_allocatorEffect hEffect
  | scratch => exact BoundedEffect.of_suspendedEffect hEffect

theorem of_boundedEffect
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState}
    (hEffect :
      BoundedEffect config depth
        (match mode with
        | .stack => depth + 1
        | .scratch _ _ => depth)
        before after) :
    ActivationEffect config depth mode before after := by
  cases mode with
  | stack =>
      exact
        { ready := hEffect.ready
          growth := hEffect.growth
          prefixStable := fun hDepth hBudget =>
            hEffect.prefixStable (Nat.lt_succ_iff.mpr hDepth) hBudget }
  | scratch =>
      exact
        { ready := hEffect.ready
          growth := hEffect.growth
          prefixStable := hEffect.prefixStable }

theorem refl
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {target : TargetState}
    (hReady : AllocatorReady config depth target) :
    ActivationEffect config depth mode target target := by
  cases mode with
  | stack => exact AllocatorEffect.refl hReady
  | scratch => exact SuspendedEffect.refl hReady

theorem trans
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {first second third : TargetState}
    (hFirst : ActivationEffect config depth mode first second)
    (hSecond : ActivationEffect config depth mode second third) :
    ActivationEffect config depth mode first third := by
  cases mode with
  | stack => exact AllocatorEffect.trans hFirst hSecond
  | scratch => exact SuspendedEffect.trans hFirst hSecond

theorem sameFrame
    {config : Config} {depth : Nat} {beforeMode afterMode : ActivationMode}
    {before after : TargetState}
    (hEffect : ActivationEffect config depth beforeMode before after)
    (hSame : SameFrame beforeMode afterMode) :
    ActivationEffect config depth afterMode before after := by
  cases hSame with
  | stack => exact hEffect
  | scratch => exact hEffect

end ActivationEffect

/-- The allocator prefix owned by one activation representation. -/
def activationProtectedBound (depth : Nat) (mode : ActivationMode) : Nat :=
  match mode with
  | .stack => depth + 1
  | .scratch _ _ => depth

/--
Outcome-indexed allocator preservation. Continuing outcomes restore the
activation's exact allocator depth. A halt may retain a deeper final depth,
because no generated continuation can observe the allocator cell, while still
protecting every caller-owned frame.
-/
inductive OutcomeEffect
    (config : Config) (depth : Nat) (mode : ActivationMode)
    (before after : TargetState) : Locals.Source.Mode -> Prop where
  | activation {outcomeMode : Locals.Source.Mode}
      (effect : ActivationEffect config depth mode before after) :
      OutcomeEffect config depth mode before after outcomeMode
  | halt (kind : Assembly.HaltKind) {finalDepth : Nat}
      (effect :
        BoundedEffect config finalDepth
          (activationProtectedBound depth mode) before after) :
      OutcomeEffect config depth mode before after (.halt kind)

namespace OutcomeEffect

theorem of_activation
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState} {outcomeMode : Locals.Source.Mode}
    (hEffect : ActivationEffect config depth mode before after) :
    OutcomeEffect config depth mode before after outcomeMode :=
  .activation hEffect

theorem halt_of_bounded
    {config : Config} {depth finalDepth : Nat} {mode : ActivationMode}
    {before after : TargetState} {kind : Assembly.HaltKind}
    (hEffect :
      BoundedEffect config finalDepth
        (activationProtectedBound depth mode) before after) :
    OutcomeEffect config depth mode before after (.halt kind) :=
  .halt kind hEffect

theorem activation_of_not_halt
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState} {outcomeMode : Locals.Source.Mode}
    (hEffect : OutcomeEffect config depth mode before after outcomeMode)
    (hNotHalt : ∀ kind, outcomeMode ≠ .halt kind) :
    ActivationEffect config depth mode before after := by
  cases hEffect with
  | activation effect => exact effect
  | halt kind _ => exact False.elim (hNotHalt kind rfl)

theorem exists_boundedEffect
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState} {outcomeMode : Locals.Source.Mode}
    (hEffect : OutcomeEffect config depth mode before after outcomeMode) :
    ∃ finalDepth,
      BoundedEffect config finalDepth
        (activationProtectedBound depth mode) before after := by
  cases hEffect with
  | activation effect =>
      cases mode <;> exact ⟨depth, effect.to_boundedEffect⟩
  | halt _ effect =>
      exact ⟨_, effect⟩

theorem mode_of_sameFrame
    {config : Config} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {before after : TargetState} {outcomeMode : Locals.Source.Mode}
    (hEffect :
      OutcomeEffect config depth beforeMode before after outcomeMode)
    (hSame : SameFrame beforeMode afterMode) :
    OutcomeEffect config depth afterMode before after outcomeMode := by
  cases hEffect with
  | activation effect => exact .activation (effect.sameFrame hSame)
  | halt kind effect => cases hSame <;> exact .halt kind effect

theorem prepend_activation
    {config : Config} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {first second third : TargetState}
    {outcomeMode : Locals.Source.Mode}
    (hFirst : ActivationEffect config depth beforeMode first second)
    (hSame : SameFrame beforeMode afterMode)
    (hSecond :
      OutcomeEffect config depth afterMode second third outcomeMode) :
    OutcomeEffect config depth beforeMode first third outcomeMode := by
  cases hSame with
  | stack =>
      cases hSecond with
      | activation effect => exact .activation (hFirst.trans effect)
      | halt kind effect =>
          exact .halt kind (hFirst.to_boundedEffect.trans effect)
  | scratch =>
      cases hSecond with
      | activation effect => exact .activation (hFirst.trans effect)
      | halt kind effect =>
          exact .halt kind (hFirst.to_boundedEffect.trans effect)

end OutcomeEffect

/-- Stack-only programs need no allocator; scratch programs use one config. -/
inductive ResourceMode where
  | stackOnly
  | scratch (config : Config)
  deriving Repr

namespace ResourceMode

def Budget : ResourceMode → Nat → Prop
  | .stackOnly, _depth => True
  | .scratch config, depth => AllocationInteractionFrame.Budget config depth

def FuelSafe (mode : ResourceMode) (fuel : Nat) : Prop :=
  mode.Budget fuel

def Ready (mode : ResourceMode) (depth : Nat)
    (target : TargetState) : Prop :=
  match mode with
  | .stackOnly => True
  | .scratch config => AllocatorReady config depth target

end ResourceMode

theorem scratchAddress_end_le_frameEnd
    {config : Config} {frameBase slot : Nat}
    (hSlot : slot < config.frameWords) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      frameBase + bytes config := by
  have hSucc : slot + 1 ≤ config.frameWords :=
    Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * config.frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ = frameBase + bytes config := rfl

/-- Relationship between one activation and the global allocator depth. -/
inductive ActivationOwned (config : Config) :
    Nat → Nat → ActivationMode → Prop where
  | stack {allocatorDepth frameBase : Nat} :
      ActivationOwned config allocatorDepth frameBase .stack
  | scratch
      {previousDepth frameBase frameDepth frameWords : Nat}
      (depth : frameBase = baseAt config previousDepth)
      (words : frameWords = config.frameWords) :
      ActivationOwned config (previousDepth + 1) frameBase
        (.scratch frameDepth frameWords)

namespace ActivationOwned

/-- An owned scratch activation uses the one frame width selected by the
compiler-owned allocator configuration. -/
theorem scratch_words
    {config : Config} {allocatorDepth frameBase frameDepth frameWords : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    frameWords = config.frameWords := by
  cases hOwned with
  | scratch _ hWords => exact hWords

theorem sameFrame {config : Config}
    {allocatorDepth frameBase : Nat} {before after : ActivationMode}
    (hOwned : ActivationOwned config allocatorDepth frameBase before)
    (hSame : SameFrame before after) :
    ActivationOwned config allocatorDepth frameBase after := by
  cases hOwned with
  | stack =>
      cases hSame
      exact .stack
  | @scratch previousDepth _ beforeDepth frameWords hBase hWords =>
      cases hSame with
      | scratch _ afterDepth _ =>
          exact .scratch hBase hWords

/-- Every spill in an owned scratch activation starts in frame storage. -/
theorem firstFrame_le_scratchAddress
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    config.firstFrame ≤ scratchAddress frameBase slot := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase _hWords =>
      rw [hBase]
      exact
        (Nat.le_add_right config.firstFrame
          (previousDepth * bytes config)).trans
          (Nat.le_add_right (baseAt config previousDepth)
            (MemoryContract.wordBytes * slot))

/-- The allocator metadata word ends before every owned scratch frame. -/
theorem allocatorCell_end_le_frameBase
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase frameDepth frameWords : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    config.allocatorCell + MemoryContract.wordBytes ≤ frameBase := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase _hWords =>
      obtain
          ⟨_reservation, _hReservation, hAllocator, hFirst, _hLimit,
            _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hConfig
      rw [hBase, baseAt, hAllocator, hFirst]
      unfold MemoryContract.ScratchReservation.allocatorCell
        MemoryContract.ScratchReservation.frameBase
      exact Nat.le_add_right _ _

theorem allocatorCell_disjoint_scratchAddress
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase frameDepth frameWords slot : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    config.allocatorCell + MemoryContract.wordBytes ≤
      scratchAddress frameBase slot :=
  (hOwned.allocatorCell_end_le_frameBase hConfig).trans
    (Nat.le_add_right frameBase (MemoryContract.wordBytes * slot))

/-- Every live spill in an owned frame ends before the next allocator base. -/
theorem scratchAddress_end_le_allocatorBase
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hSlot : slot < frameWords) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      baseAt config allocatorDepth := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase hWords =>
      rw [hBase]
      calc
        scratchAddress (baseAt config previousDepth) slot +
              MemoryContract.wordBytes ≤
            baseAt config previousDepth +
              MemoryContract.wordBytes * config.frameWords :=
          scratchAddress_end_le_frameEnd (by simpa [hWords] using hSlot)
        _ = baseAt config (previousDepth + 1) := by
          simp [baseAt, bytes, Nat.add_mul, Nat.add_assoc]

/-- An owned scratch frame ends exactly at the current allocator base. -/
theorem frameEnd_eq_allocatorBase
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    frameBase + MemoryContract.wordBytes * frameWords =
      baseAt config allocatorDepth := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase hWords =>
      rw [hBase, hWords]
      simp [baseAt, bytes, Nat.add_mul, Nat.add_assoc]

end ActivationOwned

@[simp] theorem baseAt_zero (config : Config) :
    baseAt config 0 = config.firstFrame := by
  simp [baseAt]

theorem baseAt_succ (config : Config) (depth : Nat) :
    baseAt config (depth + 1) = baseAt config depth + bytes config := by
  simp [baseAt, Nat.add_mul, Nat.add_assoc]

theorem baseAt_mono (config : Config) : Monotone (baseAt config) := by
  intro left right hLe
  unfold baseAt
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (bytes config) hLe) config.firstFrame

/-- A validated scratch configuration always admits the allocator's initial
depth. -/
theorem budget_zero_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config) :
    Budget config 0 := by
  obtain
      ⟨reservation, _hReservation, _hAllocator, hFirst, hLimit,
        hWords, _hWF, _hHost, hPositive, hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  simp only [Budget, baseAt_zero, bytes]
  rw [hFirst, hLimit, hWords]
  change frameWords ≤ reservation.words - 1 at hFits
  change 0 < reservation.words at hPositive
  change
    reservation.base + 32 + 32 * frameWords ≤
      reservation.base + 32 * reservation.words
  omega

namespace ActivationOwned

/-- A current-frame spill starts above every strictly suspended prefix. -/
theorem baseAt_le_scratchAddress_of_lt
    {config : Config}
    {allocatorDepth protectedDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hDepth : protectedDepth < allocatorDepth) :
    baseAt config protectedDepth ≤ scratchAddress frameBase slot := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase _hWords =>
      rw [hBase]
      exact
        (baseAt_mono config (by omega)).trans
          (Nat.le_add_right (baseAt config previousDepth)
            (MemoryContract.wordBytes * slot))

/-- A compiler-bounded scratch write preserves every strictly older frame. -/
theorem boundedEffect_of_scratchStoreSlot
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth readyDepth : Nat}
    {config : Config} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : SourceState} {before after : TargetState}
    {value : Word}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source before)
    (hSlot : slot < frameWords)
    (hReady : AllocatorReady config readyDepth before)
    (hMachine :
      after.evm.toMachineState =
        before.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) value) :
    BoundedEffect config readyDepth allocatorDepth before after := by
  have hSucc : slot + 1 ≤ frameWords := Nat.succ_le_iff.mpr hSlot
  have hEndLe :
      scratchAddress frameBase slot + MemoryContract.wordBytes ≤
        frameBase + MemoryContract.wordBytes * frameWords := by
    calc
      scratchAddress frameBase slot + MemoryContract.wordBytes =
          frameBase + MemoryContract.wordBytes * (slot + 1) := by
        simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
      _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
  have hEndLt :
      scratchAddress frameBase slot + MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    hEndLe.trans_lt hRel.frameNoWrap
  have hAddressLt :
      scratchAddress frameBase slot < EvmYul.UInt256.size := by
    omega
  have hHost :
      scratchAddress frameBase slot + MemoryContract.wordBytes < USize.size :=
    hEndLe.trans_lt hRel.frameHostAddressable
  exact
    BoundedEffect.of_mstore_above hReady hMachine
      (EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt)
      hHost
      (Or.inl (hOwned.allocatorCell_disjoint_scratchAddress hConfig))
      (fun hProtected =>
        hOwned.baseAt_le_scratchAddress_of_lt hProtected)

/--
One live compiler-owned scratch write preserves every strictly older frame
while retaining the allocator depth selected by the caller.
-/
theorem boundedEffect_of_scratchStore
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth readyDepth : Nat}
    {config : Config} {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : SourceState} {before after : TargetState}
    {name : Locals.Name} {value : Word}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source before)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hReady : AllocatorReady config readyDepth before)
    (hMachine :
      after.evm.toMachineState =
        before.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) value) :
    BoundedEffect config readyDepth allocatorDepth before after :=
  hOwned.boundedEffect_of_scratchStoreSlot hConfig hRel
    (hRel.scratchBound name slot hLive hLocation) hReady hMachine

end ActivationOwned

/--
Reconstruct a caller activation after a callee returns values above the exact
caller stack. Scratch locals are recovered from the protected allocator prefix.
-/
theorem resume_after_call
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {sourceBefore sourceAfter : SourceState}
    {targetBefore targetAfter : TargetState}
    {returned : List Word}
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode
        sourceBefore targetBefore)
    (hOwned : ActivationOwned config allocatorDepth frameBase mode)
    (hVars : sourceAfter.vars = sourceBefore.vars)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract
        sourceAfter.shared.toMachineState targetAfter.evm.toMachineState)
    (hWorld :
      sourceAfter.shared.toState = targetAfter.evm.toSharedState.toState)
    (hStack :
      targetAfter.evm.stack = returned ++ targetBefore.evm.stack)
    (hActiveNoWrap :
      targetAfter.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hProtected :
      ProtectedPrefix config allocatorDepth targetBefore targetAfter) :
    ActivationStateRel contract plan live returned.length frameBase mode
      sourceAfter targetAfter := by
  cases hRel with
  | stack hOnly _hBeforeNoWrap hState =>
      refine .stack hOnly hActiveNoWrap ?_
      refine
        { machine := hMachine
          world := hWorld
          store := ?_ }
      intro name location hLive hLocation
      have hOld := hState.store name location hLive hLocation
      cases location with
      | stack planDepth =>
          rcases hOld with ⟨depth, hDepth, hValue⟩
          refine ⟨depth, hDepth, ?_⟩
          rw [hStack]
          rw [List.getElem?_append_right
            (Nat.le_add_right returned.length depth)]
          simpa [hVars] using hValue
      | scratch slot =>
          exact False.elim (hOnly name slot hLive hLocation)
  | scratch hScratch =>
      refine .scratch ?_
      refine
        { base :=
            { machine := hMachine
              world := hWorld
              store := ?_ }
          framePointer := ?_
          frameActive :=
            hScratch.frameActive.trans
              (Nat.mul_le_mul_right MemoryContract.wordBytes
                hProtected.growth.active)
          frameAllocated :=
            hScratch.frameAllocated.trans hProtected.growth.memory
          frameNoWrap := hScratch.frameNoWrap
          frameHostAddressable := hScratch.frameHostAddressable
          activeNoWrap := hActiveNoWrap
          frameReserved := hScratch.frameReserved
          scratchBound := hScratch.scratchBound }
      · intro name location hLive hLocation
        have hOld := hScratch.base.store name location hLive hLocation
        cases location with
        | stack planDepth =>
            rcases hOld with ⟨depth, hDepth, hValue⟩
            refine ⟨depth, hDepth, ?_⟩
            rw [hStack]
            rw [List.getElem?_append_right
              (Nat.le_add_right returned.length depth)]
            simpa [hVars] using hValue
        | scratch slot =>
            exact
              (hProtected.lookup
                hOwned.firstFrame_le_scratchAddress
                (hOwned.scratchAddress_end_le_allocatorBase
                  (hScratch.scratchBound name slot hLive hLocation))
                ((hOwned.scratchAddress_end_le_allocatorBase
                    (hScratch.scratchBound name slot hLive hLocation)).trans
                  (by
                    rw [← hOwned.frameEnd_eq_allocatorBase]
                    exact hScratch.frameAllocated))
                ((hOwned.scratchAddress_end_le_allocatorBase
                    (hScratch.scratchBound name slot hLive hLocation)).trans
                  (by
                    rw [← hOwned.frameEnd_eq_allocatorBase]
                    exact hScratch.frameActive))).trans
                (by simpa [hVars] using hOld)
      · rw [hStack]
        rw [List.getElem?_append_right
          (Nat.le_add_right returned.length _)]
        simpa [Nat.add_assoc] using hScratch.framePointer

theorem budget_mono {config : Config} {smaller larger : Nat}
    (hDepth : smaller ≤ larger) (hBudget : Budget config larger) :
    Budget config smaller := by
  unfold Budget at hBudget ⊢
  exact Nat.le_trans
    (Nat.add_le_add_right (baseAt_mono config hDepth) (bytes config))
    hBudget

theorem noWrap_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    baseAt config depth + bytes config < EvmYul.UInt256.size := by
  obtain
    ⟨_reservation, _hReservation, _hAllocator, _hFirst, hLimit,
      _hWords, hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  exact lt_of_le_of_lt (by simpa [Budget, hLimit] using hBudget) hWF.2

theorem hostAddressable_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    baseAt config depth + bytes config < USize.size := by
  obtain
    ⟨_reservation, _hReservation, _hAllocator, _hFirst, hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  exact lt_of_le_of_lt
    (by simpa [Budget, hLimit] using hBudget) hHost

theorem reserved_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    ∃ reservation,
      contract.scratch? = some reservation ∧
        reservation.containsRegion
          (baseAt config depth) config.frameWords := by
  obtain
    ⟨reservation, hReservation, _hAllocator, hFirst, hLimit,
      _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  refine ⟨reservation, hReservation, ?_⟩
  constructor
  · unfold baseAt
    rw [hFirst]
    unfold MemoryContract.ScratchReservation.frameBase
    omega
  · rw [← hLimit]
    simpa [Budget, bytes] using hBudget

end AllocationInteractionFrame
end Functions
end EvmCompiler
