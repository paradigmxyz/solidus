import EvmCompiler.Core.MemoryContract
import EvmYul.MachineStateOps

namespace EvmCompiler
namespace Compiler
namespace MemoryRelation

def byteAt (memory : ByteArray) (address : Nat) : UInt8 :=
  memory.data.getD address 0

set_option maxHeartbeats 1000000 in
private theorem writeWord_data_eq
    (value : EvmYul.UInt256) (machine : EvmYul.MachineState)
    (address : Nat)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size) :
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.data =
      machine.memory.data.extract 0 address ++
        ((ffi.ByteArray.zeroes
            (OfNat.ofNat (address - machine.memory.size))).data ++
          (value.toByteArray.data ++
            machine.memory.data.extract
              (address + 32) machine.memory.size)) := by
  unfold EvmYul.MachineState.writeWord EvmYul.writeBytes
  simp only [hAddress]
  unfold ByteArray.write
  simp only [EvmYul.UInt256.size_toByteArray]
  simp
  have hPaddingLt :
      address - machine.memory.size <
        2 ^ System.Platform.numBits := by
    rw [← USize.size_eq_two_pow]
    omega
  have hPadding :
      (OfNat.ofNat (address - machine.memory.size) : USize).toNat =
        address - machine.memory.size := by
    exact
      USize.toNat_ofNat_of_lt'
        (by simpa [USize.size_eq_two_pow] using hPaddingLt)
  rw [hPadding]
  have hZeroSize :
      (ffi.ByteArray.zeroes
        (OfNat.ofNat (address - machine.memory.size))).data.size =
          address - machine.memory.size := by
    change
      (ffi.ByteArray.zeroes
        (OfNat.ofNat (address - machine.memory.size))).size =
          address - machine.memory.size
    rw [ffi.ByteArray.size_zeroes, hPadding]
  have hZeroPrefix :
      (ffi.ByteArray.zeroes
          (OfNat.ofNat (address - machine.memory.size))).data.extract
            0 (address - machine.memory.size) =
        (ffi.ByteArray.zeroes
          (OfNat.ofNat (address - machine.memory.size))).data := by
    have hExtract :=
      Array.extract_size
        (xs := (ffi.ByteArray.zeroes
          (OfNat.ofNat (address - machine.memory.size))).data)
    rw [hZeroSize] at hExtract
    exact hExtract
  have hValue :
      value.toByteArray.data.extract 0 32 =
        value.toByteArray.data := by
    rw [← EvmYul.UInt256.size_toByteArray value]
    exact Array.extract_size
  have hMemorySuffix :
      machine.memory.data.extract (address + 32)
          (machine.memory.size + (address - machine.memory.size)) =
        machine.memory.data.extract (address + 32)
          machine.memory.size := by
    by_cases hStart : machine.memory.size ≤ address + 32
    · rw [Array.extract_empty_of_size_le_start hStart,
        Array.extract_empty_of_size_le_start hStart]
    · have hAddressLe : address ≤ machine.memory.size := by omega
      simp [Nat.sub_eq_zero_of_le hAddressLe]
  have hZeroSuffix :
      (ffi.ByteArray.zeroes
          (OfNat.ofNat (address - machine.memory.size))).data.extract
            (address + 32 - machine.memory.size)
            (address - machine.memory.size) =
        #[] := by
    apply Array.extract_empty_of_size_le_start
    rw [hZeroSize]
    omega
  rw [hZeroPrefix, hValue, hMemorySuffix, hZeroSuffix]
  simp

theorem byteAt_writeWord_of_outside
    (value : EvmYul.UInt256) (machine : EvmYul.MachineState)
    (address query : Nat)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hOutside : query < address ∨ address + 32 ≤ query) :
    byteAt
        (machine.writeWord
          (EvmYul.UInt256.ofNat address) value).memory query =
      byteAt machine.memory query := by
  rw [byteAt,
    writeWord_data_eq value machine address hAddress hHost,
    byteAt]
  have hPadding :
      (OfNat.ofNat (address - machine.memory.size) : USize).toNat =
        address - machine.memory.size := by
    apply USize.toNat_ofNat_of_lt'
    omega
  let pre := machine.memory.data.extract 0 address
  let pad :=
    (ffi.ByteArray.zeroes
      (OfNat.ofNat (address - machine.memory.size))).data
  let bytes := value.toByteArray.data
  let post :=
    machine.memory.data.extract (address + 32) machine.memory.size
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  change
    (pre ++ (pad ++ (bytes ++ post)))[query]?.getD 0 =
      machine.memory.data[query]?.getD 0
  have hPrefixSize :
      pre.size = min address machine.memory.size := by
    simp [pre, Array.size_extract]
  have hPaddingSize :
      pad.size = address - machine.memory.size := by
    simp [pad, ffi.ByteArray.size_zeroes, hPadding]
  have hWordSize : bytes.size = 32 := by
    simp [bytes]
  have hSuffixSize :
      post.size = machine.memory.size - (address + 32) := by
    simp [post, Array.size_extract]
  rcases hOutside with hBefore | hAfter
  · by_cases hMemory : query < machine.memory.size
    · have hPrefix : query < pre.size := by
        rw [hPrefixSize]
        exact lt_min hBefore hMemory
      rw [Array.getElem?_append_left hPrefix]
      simp [pre, hBefore, hMemory]
    · have hMin :
          min address machine.memory.size = machine.memory.size :=
        Nat.min_eq_right (by omega)
      have hInside :
          query - machine.memory.size <
            address - machine.memory.size := by
        omega
      have hPastPrefix : pre.size ≤ query := by
        rw [hPrefixSize, hMin]
        omega
      rw [Array.getElem?_append_right hPastPrefix]
      have hInPadding :
          query - pre.size < pad.size := by
        rw [hPrefixSize, hPaddingSize, hMin]
        exact hInside
      rw [Array.getElem?_append_left hInPadding]
      have hZeroIndex :
          query - pre.size <
            (OfNat.ofNat
              (address - machine.memory.size) : USize).toNat := by
        rw [hPadding]
        rw [← hPaddingSize]
        exact hInPadding
      simp only [pad, ffi.ByteArray.data_getElem?_zeroes]
      rw [if_pos hZeroIndex]
      simp [hMemory]
  · by_cases hMemory : query < machine.memory.size
    · have hMin :
          min address machine.memory.size = address :=
        Nat.min_eq_left (by omega)
      have hPad : address - machine.memory.size = 0 :=
        Nat.sub_eq_zero_of_le (by omega)
      have hPastPrefix : pre.size ≤ query := by
        rw [hPrefixSize, hMin]
        omega
      rw [Array.getElem?_append_right hPastPrefix]
      have hPastPadding :
          pad.size ≤ query - pre.size := by
        rw [hPaddingSize, hPad]
        omega
      rw [Array.getElem?_append_right hPastPadding]
      have hPastWord :
          bytes.size ≤ query - pre.size - pad.size := by
        rw [hWordSize, hPrefixSize, hPaddingSize, hMin, hPad]
        omega
      rw [Array.getElem?_append_right hPastWord]
      have hPostInside :
          query - address - 32 <
            machine.memory.size - (address + 32) := by
        omega
      have hPostIndex :
          address + 32 + (query - address - 32) = query := by
        omega
      rw [show
        post[query - pre.size - pad.size - bytes.size]? =
          machine.memory.data[query]? by
        simp only [post, Array.getElem?_extract, hPrefixSize,
          hPaddingSize, hWordSize, hMin, hPad]
        have hMemorySize :
            machine.memory.data.size = machine.memory.size := by
          cases machine.memory
          rfl
        rw [hMemorySize, min_self]
        simp only [Nat.sub_zero]
        rw [if_pos hPostInside]
        rw [hPostIndex]]
    · by_cases hAddressMemory : address < machine.memory.size
      · have hMin :
            min address machine.memory.size = address :=
          Nat.min_eq_left (Nat.le_of_lt hAddressMemory)
        have hPad : address - machine.memory.size = 0 :=
          Nat.sub_eq_zero_of_le (Nat.le_of_lt hAddressMemory)
        have hPastPrefix : pre.size ≤ query := by
          rw [hPrefixSize, hMin]
          omega
        rw [Array.getElem?_append_right hPastPrefix]
        have hPastPadding :
            pad.size ≤ query - pre.size := by
          rw [hPaddingSize, hPad]
          omega
        rw [Array.getElem?_append_right hPastPadding]
        have hPastWord :
            bytes.size ≤ query - pre.size - pad.size := by
          rw [hWordSize, hPrefixSize, hPaddingSize, hMin, hPad]
          omega
        rw [Array.getElem?_append_right hPastWord]
        have hPastSuffix :
            post.size ≤
              query - pre.size - pad.size - bytes.size := by
          rw [hSuffixSize, hPrefixSize, hPaddingSize, hWordSize,
            hMin, hPad]
          omega
        rw [show
          post[query - pre.size - pad.size - bytes.size]? =
            none by
          exact Array.getElem?_eq_none hPastSuffix]
        simp [hMemory]
      · have hMin :
            min address machine.memory.size = machine.memory.size :=
          Nat.min_eq_right (by omega)
        have hPastPrefix : pre.size ≤ query := by
          rw [hPrefixSize, hMin]
          omega
        rw [Array.getElem?_append_right hPastPrefix]
        have hPastPadding :
            pad.size ≤ query - pre.size := by
          rw [hPaddingSize, hPrefixSize, hMin]
          omega
        rw [Array.getElem?_append_right hPastPadding]
        have hPastWord :
            bytes.size ≤ query - pre.size - pad.size := by
          rw [hWordSize, hPrefixSize, hPaddingSize, hMin]
          omega
        rw [Array.getElem?_append_right hPastWord]
        have hSuffixEmpty : post = #[] := by
          apply Array.extract_empty_of_size_le_start
          change machine.memory.size ≤ address + 32
          omega
        simp [hSuffixEmpty, hMemory]

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

theorem trans {reservation : MemoryContract.ScratchReservation}
    {first second third : ByteArray}
    (hLeft : OutsideReservation reservation first second)
    (hRight : OutsideReservation reservation second third) :
    OutsideReservation reservation first third := by
  intro address hOutside
  exact (hLeft address hOutside).trans (hRight address hOutside)

theorem writeWord_right
    {reservation : MemoryContract.ScratchReservation}
    {source : ByteArray} (target : EvmYul.MachineState)
    (address : Nat) (value : EvmYul.UInt256)
    (hRel : OutsideReservation reservation source target.memory)
    (hRegion : reservation.containsRegion address 1)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size) :
    OutsideReservation reservation source
      (target.writeWord
        (EvmYul.UInt256.ofNat address) value).memory := by
  intro query hOutside
  rw [hRel query hOutside]
  apply Eq.symm
  apply byteAt_writeWord_of_outside value target address query hAddress
  · simpa [MemoryContract.wordBytes] using hHost
  · by_contra hInsideWord
    simp only [not_or, not_lt] at hInsideWord
    apply hOutside
    rcases hRegion with ⟨hBase, hEnd⟩
    have hQueryEnd :
        query < address + MemoryContract.wordBytes := by
      simpa [MemoryContract.wordBytes] using
        (show query < address + 32 by omega)
    exact
      ⟨Nat.le_trans hBase hInsideWord.1,
        lt_of_lt_of_le hQueryEnd hEnd⟩

end OutsideReservation

theorem activeWords_toNat_le_mstore
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size) :
    machine.activeWords.toNat ≤
      (machine.mstore
        (EvmYul.UInt256.ofNat address) value).activeWords.toNat := by
  have hAddressLt : address < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt (Nat.le_add_right address _) hEnd
  have hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address :=
    EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
  have hEnd32 : address + 32 < EvmYul.UInt256.size := by
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
    machine.activeWords.toNat ≤
      (EvmYul.UInt256.ofNat
        (EvmYul.MachineState.M
          machine.activeWords.toNat address 32)).toNat
  rw [EvmYul.UInt256.toNat_ofNat_of_lt hM]
  simp [EvmYul.MachineState.M]

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

theorem mstore_target
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    {reservation : MemoryContract.ScratchReservation}
    (address : Nat) (value : EvmYul.UInt256)
    (hRel : MachineRel contract source target)
    (hReservation : contract.scratch? = some reservation)
    (hRegion : reservation.containsRegion address 1)
    (hEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hHost :
      address + MemoryContract.wordBytes < USize.size) :
    MachineRel contract source
      (target.mstore (EvmYul.UInt256.ofNat address) value) := by
  have hAddressLt : address < EvmYul.UInt256.size :=
    lt_of_le_of_lt (Nat.le_add_right address _) hEnd
  have hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address :=
    EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
  have hMemory :
      OutsideReservation reservation source.memory target.memory := by
    simpa [hReservation] using hRel.memory
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hReservation]
    simpa [EvmYul.MachineState.mstore] using
      (OutsideReservation.writeWord_right target address value
        hMemory hRegion hAddress hHost)
  · rw [hReservation]
    have hBefore :
        source.activeWords.toNat ≤ target.activeWords.toNat := by
      simpa [hReservation] using hRel.activeWords
    exact hBefore.trans
      (activeWords_toNat_le_mstore target address value hEnd)
  · simpa [EvmYul.MachineState.mstore] using hRel.returnData
  · simpa [EvmYul.MachineState.mstore] using hRel.output

end MachineRel

end MemoryRelation
end Compiler
end EvmCompiler
