import EvmCompiler.Compiler.MemoryRelation
import EvmCompiler.Functions.AllocationSupport
import EvmCompiler.Functions.ObserverSemantics
import EvmCompiler.Structured.ObserverSemantics
import EvmYul.MachineStateOps

namespace EvmCompiler
namespace Functions
namespace AllocationObserverRelation

/-!
State and resource contracts for the adjacent Functions-to-allocated-
Expressions boundary.

The source owns named variables and the target realizes only the currently
live names through the checked allocation plan. Stack locations are indexed
from the top of the concrete EVM stack. Scratch locations are indexed from the
current activation's private frame base.

This module deliberately defines no lowering and no execution interpreter.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word
abbrev Plan := Locals.Allocation.Plan
abbrev Location := Locals.Allocation.LocalLocation
abbrev SourceState := Functions.ObserverSemantics.State
abbrev TargetState := Structured.ObserverSemantics.State

def scratchAddress (frameBase slot : Nat) : Nat :=
  frameBase + MemoryContract.wordBytes * slot

def locationValue? (stackOffset frameBase : Nat)
    (target : Structured.RunState) : Location → Option Word
  | .stack depth =>
      target.evm.stack[stackOffset + depth]?
  | .scratch slot =>
      some
        (target.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)))

/--
Realization of the source store for names that are live at the current
semantic point.

Allocation plans describe an entire lexical scope, including declarations
that may not have executed yet. Indexing by `live` avoids requiring target
values for those future declarations.
-/
def StoreRel (plan : Plan) (live : List Locals.Name)
    (stackOffset frameBase : Nat) (source : Locals.Source.State)
    (target : Structured.RunState) : Prop :=
  ∀ name location,
    name ∈ live →
    plan.location? name = some location →
    locationValue? stackOffset frameBase target location = source.vars name

structure CoreRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : Locals.Source.State) (target : Structured.RunState) :
    Prop where
  machine :
    Compiler.MemoryRelation.MachineRel contract
      source.shared.toMachineState
      target.evm.toMachineState
  store : StoreRel plan live stackOffset frameBase source target

structure StateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  cursor : source.cursor = target.cursor
  core :
    CoreRel contract plan live stackOffset frameBase
      source.source target.source

namespace StoreRel

theorem mono {plan : Plan} {smaller larger : List Locals.Name}
    {stackOffset frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState}
    (hRel : StoreRel plan larger stackOffset frameBase source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
    StoreRel plan smaller stackOffset frameBase source target := by
  intro name location hLive hLocation
  exact hRel name location (hSubset name hLive) hLocation

theorem stack {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState} {name : Locals.Name} {depth : Nat}
    (hRel : StoreRel plan live stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack depth)) :
    target.evm.stack[stackOffset + depth]? = source.vars name :=
  hRel name (.stack depth) hLive hLocation

theorem scratch {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState} {name : Locals.Name} {slot : Nat}
    (hRel : StoreRel plan live stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    target.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
      (source.vars name).getD (EvmYul.UInt256.ofNat 0) := by
  have hValue := hRel name (.scratch slot) hLive hLocation
  simp only [locationValue?] at hValue
  rw [← hValue]
  simp

end StoreRel

namespace StateRel

def pushTargetBy {transcript : Trace} (pcDelta : Nat) (value : Word)
    (target : TargetState transcript) : TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (target.source.evm.replaceStackAndIncrPC
        (value :: target.source.evm.stack) (pcΔ := pcDelta)))

def pushTarget {transcript : Trace} (value : Word)
    (target : TargetState transcript) : TargetState transcript :=
  pushTargetBy 1 value target

def contractTargetBy {transcript : Trace} (pcDelta : Nat)
    (value : Word) (rest : List Word)
    (target : TargetState transcript) : TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (target.source.evm.replaceStackAndIncrPC
        (value :: rest) (pcΔ := pcDelta)))

def mstoreTarget {transcript : Trace}
    (address value : Word) (rest : List Word)
    (target : TargetState transcript) : TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (({ target.source.evm with
          toMachineState :=
            target.source.evm.toMachineState.mstore address value }).replaceStackAndIncrPC
        rest))

theorem mono {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {smaller larger : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      StateRel contract plan larger stackOffset frameBase source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
    StateRel contract plan smaller stackOffset frameBase source target :=
  ⟨hRel.cursor,
    ⟨hRel.core.machine, hRel.core.store.mono hSubset⟩⟩

theorem push_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (pcDelta : Nat) (value : Word)
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (pushTargetBy pcDelta value target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [pushTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.machine
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack depth =>
        change
          (value :: target.source.evm.stack)[stackOffset + 1 + depth]? =
            source.source.vars name
        rw [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega]
        simpa using hValue
    | scratch slot =>
        simpa [locationValue?, pushTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem push_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (value : Word)
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (pushTarget value target) := by
  exact push_target_by 1 value hRel

theorem contract_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {right left value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 2) frameBase
        source target)
    (hStack : target.source.evm.stack = right :: left :: rest)
    (pcDelta : Nat) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (contractTargetBy pcDelta value rest target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.machine
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack depth =>
        change
          (value :: rest)[stackOffset + 1 + depth]? =
            source.source.vars name
        change
          target.source.evm.stack[stackOffset + 2 + depth]? =
            source.source.vars name at hValue
        rw [hStack] at hValue
        have hRest :
            rest[stackOffset + depth]? = source.source.vars name := by
          simpa [show stackOffset + 2 + depth =
              (stackOffset + depth) + 2 by omega] using hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hRest
    | scratch slot =>
        simpa [locationValue?, contractTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem replace_top_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {old value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 1) frameBase
        source target)
    (hStack : target.source.evm.stack = old :: rest)
    (pcDelta : Nat) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (contractTargetBy pcDelta value rest target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.machine
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack depth =>
        change
          (value :: rest)[stackOffset + 1 + depth]? =
            source.source.vars name
        change
          target.source.evm.stack[stackOffset + 1 + depth]? =
            source.source.vars name at hValue
        rw [hStack] at hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hValue
    | scratch slot =>
        simpa [locationValue?, contractTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem consume_forward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source source' : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, source')) :
    ∃ target' : TargetState transcript,
      Simulation.ResourceReplay.consume? kind target =
          some (value, target') ∧
        StateRel contract plan live stackOffset frameBase
          source' target' := by
  obtain ⟨target', hTarget, hCursor, hCore⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.cursor hRel.core hConsume
  exact ⟨target', hTarget, hCursor, hCore⟩

theorem consume_backward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source : SourceState transcript}
    {target target' : TargetState transcript}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind target =
        some (value, target')) :
    ∃ source' : SourceState transcript,
      Simulation.ResourceReplay.consume? kind source =
          some (value, source') ∧
        StateRel contract plan live stackOffset frameBase
          source' target' := by
  obtain ⟨source', hSource, hCursor, hCore⟩ :=
    Simulation.ResourceReplay.consume?_rel
      (rel := fun target source =>
        CoreRel contract plan live stackOffset frameBase source target)
      hRel.cursor.symm hRel.core hConsume
  exact ⟨source', hSource, hCursor.symm, hCore⟩

end StateRel

/--
Additional realization facts for an activation that owns a scratch frame.

The hidden frame pointer is below any temporary expression results by
`stackOffset + frameDepth`. Frame acquisition preallocates every frame word,
so reads of compiler-owned slots do not subsequently change `MSIZE`.
-/
structure ScratchStateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase frameDepth frameWords : Nat)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  base :
    StateRel contract plan live stackOffset frameBase source target
  framePointer :
    target.source.evm.stack[stackOffset + frameDepth]? =
      some (EvmYul.UInt256.ofNat frameBase)
  frameActive :
    frameBase + MemoryContract.wordBytes * frameWords ≤
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes
  frameNoWrap :
    frameBase + MemoryContract.wordBytes * frameWords <
      EvmYul.UInt256.size
  scratchBound :
    ∀ name slot,
      name ∈ live →
      plan.location? name = some (.scratch slot) →
      slot < frameWords

namespace ScratchStateRel

theorem of_wellFormed
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {regionBase : Locals.Allocation.RegionBase}
    {source : SourceState transcript} {target : TargetState transcript}
    (hBase :
      StateRel contract plan live stackOffset frameBase source target)
    (hFramePointer :
      target.source.evm.stack[stackOffset + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase))
    (hFrameActive :
      frameBase + MemoryContract.wordBytes * frameWords ≤
        target.source.evm.activeWords.toNat * MemoryContract.wordBytes)
    (hFrameNoWrap :
      frameBase + MemoryContract.wordBytes * frameWords <
        EvmYul.UInt256.size)
    (hWF : plan.WellFormed)
    (hRegion :
      plan.scratchRegion? =
        some
          { base := regionBase
            words := frameWords }) :
    ScratchStateRel contract plan live stackOffset frameBase
      frameDepth frameWords source target :=
  ⟨hBase, hFramePointer, hFrameActive, hFrameNoWrap,
    fun name slot _hLive hLocation =>
      plan.scratch_bound_of_wellFormed hWF hLocation hRegion⟩

private theorem memoryWords_eq_of_region_active
    {active address : Nat}
    (hActive :
      address + MemoryContract.wordBytes ≤
        active * MemoryContract.wordBytes) :
    EvmYul.MachineState.M active address 32 = active := by
  simp only [EvmYul.MachineState.M, MemoryContract.wordBytes]
  rw [max_eq_left]
  rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 32)]
  simp only [MemoryContract.wordBytes] at hActive
  omega

private theorem uint256_ofNat_toNat (value : Word) :
    EvmYul.UInt256.ofNat value.toNat = value := by
  cases value with
  | mk val =>
      unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
      simp
      rfl

theorem scratchAddress_end_le_active {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      target.source.evm.activeWords.toNat *
        MemoryContract.wordBytes := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ ≤ target.source.evm.activeWords.toNat *
        MemoryContract.wordBytes :=
      hRel.frameActive

theorem scratchAddress_end_lt_size {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  exact
    lt_of_le_of_lt
      (show
        scratchAddress frameBase slot + MemoryContract.wordBytes ≤
          frameBase + MemoryContract.wordBytes * frameWords by
        calc
          scratchAddress frameBase slot + MemoryContract.wordBytes =
              frameBase + MemoryContract.wordBytes * (slot + 1) := by
                simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
          _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
              frameBase)
      hRel.frameNoWrap

theorem mload_machine_eq {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    target.source.evm.toMachineState.mload
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
      (target.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)),
        target.source.evm.toMachineState) := by
  have hEndActive :=
    hRel.scratchAddress_end_le_active hLive hLocation
  have hEndLt :=
    hRel.scratchAddress_end_lt_size hLive hLocation
  have hAddressLt :
      scratchAddress frameBase slot < EvmYul.UInt256.size :=
    lt_of_lt_of_le
      (Nat.lt_add_of_pos_right
        (by decide : 0 < MemoryContract.wordBytes))
      (Nat.le_of_lt hEndLt)
  have hAddressToNat :
      (EvmYul.UInt256.ofNat
        (scratchAddress frameBase slot)).toNat =
          scratchAddress frameBase slot :=
    EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
  have hWords :
      EvmYul.MachineState.M
          target.source.evm.activeWords.toNat
          (scratchAddress frameBase slot)
          32 =
        target.source.evm.activeWords.toNat :=
    memoryWords_eq_of_region_active hEndActive
  simp [EvmYul.MachineState.mload, hAddressToNat, hWords,
    uint256_ofNat_toNat]

theorem mono {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {smaller larger : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan larger stackOffset frameBase
        frameDepth frameWords source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
    ScratchStateRel contract plan smaller stackOffset frameBase
      frameDepth frameWords source target :=
  ⟨hRel.base.mono hSubset, hRel.framePointer, hRel.frameActive,
    hRel.frameNoWrap,
    fun name slot hLive hLocation =>
      hRel.scratchBound name slot (hSubset name hLive) hLocation⟩

theorem push_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (pcDelta : Nat) (value : Word)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.pushTargetBy pcDelta value target) := by
  refine
    ⟨hRel.base.push_target_by pcDelta value, ?_, ?_,
      hRel.frameNoWrap, hRel.scratchBound⟩
  · change
      (value :: target.source.evm.stack)[stackOffset + 1 + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    rw [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega]
    simpa using hRel.framePointer
  · simpa [StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive

theorem push_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (value : Word)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.pushTarget value target) := by
  exact hRel.push_target_by 1 value

theorem contract_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {right left value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 2) frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = right :: left :: rest)
    (pcDelta : Nat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.contractTargetBy pcDelta value rest target) := by
  refine
    ⟨hRel.base.contract_target_by hStack pcDelta, ?_, ?_,
      hRel.frameNoWrap, hRel.scratchBound⟩
  · change
      (value :: rest)[stackOffset + 1 + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    have hPointer := hRel.framePointer
    rw [hStack] at hPointer
    have hRest :
        rest[stackOffset + frameDepth]? =
          some (EvmYul.UInt256.ofNat frameBase) := by
      simpa [show stackOffset + 2 + frameDepth =
          (stackOffset + frameDepth) + 2 by omega] using hPointer
    simpa [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega] using hRest
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive

theorem replace_top_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {old value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = old :: rest)
    (pcDelta : Nat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.contractTargetBy pcDelta value rest target) := by
  refine
    ⟨hRel.base.replace_top_by hStack pcDelta, ?_, ?_,
      hRel.frameNoWrap, hRel.scratchBound⟩
  · change
      (value :: rest)[stackOffset + 1 + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    have hPointer := hRel.framePointer
    rw [hStack] at hPointer
    simpa [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega] using hPointer
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive

theorem consume_forward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source source' : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, source')) :
    ∃ target' : TargetState transcript,
      Simulation.ResourceReplay.consume? kind target =
          some (value, target') ∧
        ScratchStateRel contract plan live stackOffset frameBase
          frameDepth frameWords source' target' := by
  obtain ⟨target', hTarget, hBase⟩ :=
    hRel.base.consume_forward hConsume
  have hTargetSource : target'.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTarget
  refine
    ⟨target', hTarget, hBase, ?_, ?_, hRel.frameNoWrap,
      hRel.scratchBound⟩
  · simpa [hTargetSource] using hRel.framePointer
  · simpa [hTargetSource] using hRel.frameActive

theorem consume_backward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source : SourceState transcript}
    {target target' : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind target =
        some (value, target')) :
    ∃ source' : SourceState transcript,
      Simulation.ResourceReplay.consume? kind source =
          some (value, source') ∧
        ScratchStateRel contract plan live stackOffset frameBase
          frameDepth frameWords source' target' := by
  obtain ⟨source', hSource, hBase⟩ :=
    hRel.base.consume_backward hConsume
  have hTargetSource : target'.source = target.source :=
    Simulation.ResourceReplay.consume?_source hConsume
  refine
    ⟨source', hSource, hBase, ?_, ?_, hRel.frameNoWrap,
      hRel.scratchBound⟩
  · simpa [hTargetSource] using hRel.framePointer
  · simpa [hTargetSource] using hRel.frameActive

end ScratchStateRel

inductive ModeRel :
    Locals.Source.Mode → Structured.Mode → Prop where
  | regular : ModeRel .regular .regular
  | brk : ModeRel .brk .brk
  | cont : ModeRel .cont .cont
  | leave : ModeRel .leave .leave
  | halt (kind : Assembly.HaltKind) :
      ModeRel (.halt kind) (.halt kind)

structure OutcomeRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : Functions.ObserverSemantics.Outcome
      (SourceState transcript))
    (target : Structured.ObserverSemantics.Outcome
      (transcript := transcript)) : Prop where
  state :
    StateRel contract plan live stackOffset frameBase
      source.state target.state
  mode : ModeRel source.mode target.mode

namespace Frame

abbrev Config := AllocationSupport.ScratchFrameConfig

def bytes (config : Config) : Nat :=
  MemoryContract.wordBytes * config.frameWords

/--
Allocator value after `depth` active scratch frames.

The allocator cell initially contains `firstFrame`. Acquiring a frame returns
the current value and advances the cell by one fixed frame width.
-/
def baseAt (config : Config) (depth : Nat) : Nat :=
  config.firstFrame + depth * bytes config

def Budget (config : Config) (depth : Nat) : Prop :=
  baseAt config depth + bytes config ≤ config.limit

def AllocatorAt {transcript : Trace} (config : Config) (depth : Nat)
    (target : TargetState transcript) : Prop :=
  target.source.evm.toMachineState.lookupMemory
      (EvmYul.UInt256.ofNat config.allocatorCell) =
    EvmYul.UInt256.ofNat (baseAt config depth)

theorem mstore_end_le_activeBytes
    {machine : EvmYul.MachineState} {address : Nat} {value : Word}
    (hEnd : address + MemoryContract.wordBytes < EvmYul.UInt256.size) :
    address + MemoryContract.wordBytes ≤
      (machine.mstore (EvmYul.UInt256.ofNat address) value).activeWords.toNat *
        MemoryContract.wordBytes := by
  have hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address :=
    EvmYul.UInt256.toNat_ofNat_of_lt
      (lt_of_le_of_lt (Nat.le_add_right address _) hEnd)
  have hEnd32 :
      address + 32 < EvmYul.UInt256.size := by
    simpa [MemoryContract.wordBytes] using hEnd
  have hM :
      EvmYul.MachineState.M machine.activeWords.toNat address 32 <
        EvmYul.UInt256.size := by
    simp only [EvmYul.MachineState.M]
    exact Nat.max_lt.mpr
      ⟨machine.activeWords.val.isLt,
        lt_of_le_of_lt (by omega) hEnd32⟩
  simp only [EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, hAddress]
  change
    address + 32 ≤
      (EvmYul.UInt256.ofNat
        (EvmYul.MachineState.M machine.activeWords.toNat address 32)).toNat *
        32
  rw [EvmYul.UInt256.toNat_ofNat_of_lt hM]
  simp only [EvmYul.MachineState.M]
  omega

@[simp] theorem baseAt_zero (config : Config) :
    baseAt config 0 = config.firstFrame := by
  simp [baseAt]

theorem baseAt_succ (config : Config) (depth : Nat) :
    baseAt config (depth + 1) = baseAt config depth + bytes config := by
  simp [baseAt, Nat.add_mul, Nat.add_assoc]

theorem baseAt_mono (config : Config) :
    Monotone (baseAt config) := by
  intro left right hLe
  unfold baseAt
  exact
    Nat.add_le_add_left
      (Nat.mul_le_mul_right (bytes config) hLe)
      config.firstFrame

theorem budget_base_le_limit {config : Config} {depth : Nat}
    (hBudget : Budget config depth) :
    baseAt config depth ≤ config.limit :=
  Nat.le_trans (Nat.le_add_right _ _) hBudget

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

theorem scratchAddress_end_le_limit
    {config : Config} {depth slot : Nat}
    (hBudget : Budget config depth)
    (hSlot : slot < config.frameWords) :
    scratchAddress (baseAt config depth) slot +
        MemoryContract.wordBytes ≤
      config.limit :=
  Nat.le_trans (scratchAddress_end_le_frameEnd hSlot) hBudget

theorem budget_of_succ {config : Config} {depth : Nat}
    (hBudget : Budget config (depth + 1)) :
    Budget config depth := by
  unfold Budget at hBudget ⊢
  rw [baseAt_succ] at hBudget
  exact
    Nat.le_trans
      (Nat.le_add_right
        (baseAt config depth + bytes config) (bytes config))
      (by
        simpa [Nat.add_assoc] using hBudget)

theorem budget_mono {config : Config} {smaller larger : Nat}
    (hDepth : smaller ≤ larger)
    (hBudget : Budget config larger) :
    Budget config smaller := by
  unfold Budget at hBudget ⊢
  exact
    Nat.le_trans
      (Nat.add_le_add_right (baseAt_mono config hDepth) (bytes config))
      hBudget

/--
Source-facing resource premise for a run with the given call fuel.

Functions evaluation decreases fuel before recursive calls, so every active
scratch-frame depth is bounded by the initial fuel. `depth_safe` turns that
semantic bound into the concrete reservation bound required by frame
acquisition.
-/
def FuelSafe (config : Config) (fuel : Nat) : Prop :=
  Budget config fuel

theorem FuelSafe.depth_safe {config : Config} {fuel depth : Nat}
    (hSafe : FuelSafe config fuel) (hDepth : depth ≤ fuel) :
    Budget config depth :=
  budget_mono hDepth hSafe

theorem budget_zero_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config) :
    Budget config 0 := by
  obtain
    ⟨reservation, _hReservation, hAllocator, hFirst, hLimit,
      hWords, _hWF, hPositive, hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  simp only [Budget, baseAt_zero, bytes]
  rw [hFirst, hLimit, hWords]
  change frameWords ≤ reservation.words - 1 at hFits
  change 0 < reservation.words at hPositive
  change
    reservation.base + 32 + 32 * frameWords ≤
      reservation.base + 32 * reservation.words
  omega

theorem noWrap_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    baseAt config depth + bytes config < EvmYul.UInt256.size := by
  obtain
    ⟨reservation, _hReservation, _hAllocator, _hFirst, hLimit,
      _hWords, hWF, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  exact lt_of_le_of_lt (by simpa [Budget, hLimit] using hBudget) hWF.2

end Frame

end AllocationObserverRelation
end Functions
end EvmCompiler
