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

end ProtectedPrefix

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

end BoundedEffect

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

theorem budget_mono {config : Config} {smaller larger : Nat}
    (hDepth : smaller ≤ larger) (hBudget : Budget config larger) :
    Budget config smaller := by
  unfold Budget at hBudget ⊢
  exact Nat.le_trans
    (Nat.add_le_add_right (baseAt_mono config hDepth) (bytes config))
    hBudget

end AllocationInteractionFrame
end Functions
end EvmCompiler
