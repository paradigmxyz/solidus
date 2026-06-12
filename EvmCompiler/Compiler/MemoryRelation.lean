import EvmCompiler.Core.MemoryContract
import EvmYul.MachineState

namespace EvmCompiler
namespace Compiler
namespace MemoryRelation

def byteAt (memory : ByteArray) (address : Nat) : UInt8 :=
  memory.data.getD address 0

def OutsideReservation
    (reservation : MemoryContract.ScratchReservation)
    (source target : ByteArray) : Prop :=
  ∀ address,
    ¬ reservation.containsByte address →
      byteAt source address = byteAt target address

namespace OutsideReservation

theorem refl (reservation : MemoryContract.ScratchReservation)
    (memory : ByteArray) :
    OutsideReservation reservation memory memory := by
  intro _address _hOutside
  rfl

theorem symm {reservation : MemoryContract.ScratchReservation}
    {source target : ByteArray}
    (hRel : OutsideReservation reservation source target) :
    OutsideReservation reservation target source := by
  intro address hOutside
  exact (hRel address hOutside).symm

end OutsideReservation

/--
Machine-state relation used across allocation lowering.

Remaining gas is intentionally unobservable here: exact `gas()` values live in
the ordered replay transcript. Stack allocation keeps memory and active size
equal. Scratch allocation permits differences only inside the source-reserved
interval and permits target memory expansion beyond the source extent.
-/
structure MachineRel (contract : MemoryContract.Contract)
    (source target : EvmYul.MachineState) : Prop where
  memory :
    match contract.scratch? with
    | none =>
        source.memory = target.memory
    | some reservation =>
        OutsideReservation reservation source.memory target.memory
  activeWords :
    match contract.scratch? with
    | none =>
        source.activeWords = target.activeWords
    | some _reservation =>
        source.activeWords.toNat ≤ target.activeWords.toNat
  returnData : source.returnData = target.returnData
  output : source.H_return = target.H_return

namespace MachineRel

theorem refl (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    MachineRel contract machine machine := by
  constructor
  · cases hReservation : contract.scratch? with
    | none =>
        rfl
    | some reservation =>
        exact OutsideReservation.refl reservation machine.memory
  · cases contract.scratch? <;> simp
  · rfl
  · rfl

theorem of_eq {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hEq : source = target) :
    MachineRel contract source target := by
  subst target
  exact refl contract source

theorem memory_eq_of_unrestricted
    {source target : EvmYul.MachineState}
    (hRel : MachineRel MemoryContract.unrestricted source target) :
    source.memory = target.memory := by
  exact hRel.memory

theorem activeWords_eq_of_unrestricted
    {source target : EvmYul.MachineState}
    (hRel : MachineRel MemoryContract.unrestricted source target) :
    source.activeWords = target.activeWords := by
  exact hRel.activeWords

end MachineRel

end MemoryRelation
end Compiler
end EvmCompiler
