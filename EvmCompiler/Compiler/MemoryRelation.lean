import EvmCompiler.Core.MemoryContract
import EvmYul.MachineStateOps

namespace EvmCompiler
namespace Compiler
namespace MemoryRelation

def byteAt (memory : ByteArray) (address : Nat) : UInt8 :=
  memory.data.getD address 0

set_option maxHeartbeats 1000000 in
theorem writeWord_memory_data
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
    writeWord_memory_data value machine address hAddress hHost,
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

theorem writeWord_memory_size_eq_of_end_le
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hEnd : address + 32 ≤ machine.memory.size) :
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.size =
      machine.memory.size := by
  change
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.data.size =
      machine.memory.size
  rw [writeWord_memory_data value machine address hAddress hHost]
  have hAddressLe : address ≤ machine.memory.size := by omega
  have hPadding : address - machine.memory.size = 0 :=
    Nat.sub_eq_zero_of_le hAddressLe
  have hPrefix :
      (machine.memory.data.extract 0 address).size = address := by
    simp [Array.size_extract, Nat.min_eq_left hAddressLe]
  have hZero :
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).data.size = 0 := by
    change
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).size = 0
    rw [ffi.ByteArray.size_zeroes, hPadding]
    rfl
  have hWord : value.toByteArray.data.size = 32 :=
    EvmYul.UInt256.size_toByteArray value
  have hSuffix :
      (machine.memory.data.extract
        (address + 32) machine.memory.size).size =
          machine.memory.size - (address + 32) := by
    simp [Array.size_extract]
  simp only [Array.size_append]
  rw [hPrefix, hZero, hWord, hSuffix]
  omega

private theorem readWithPadding_word_eq_extract
    (memory : ByteArray) (address : Nat)
    (hEnd : address + 32 ≤ memory.size) :
    memory.readWithPadding address 32 =
      memory.extract address (address + 32) := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp only [show ¬ 32 ≥ 2 ^ 64 by omega, if_false]
  rw [if_neg (by omega : ¬ address ≥ memory.size)]
  have hSize : 32 ≤ memory.size := by omega
  rw [Nat.min_eq_left hSize]
  have hExtract :
      (memory.extract address (address + 32)).size = 32 := by
    simp
    omega
  rw [hExtract]
  apply ByteArray.ext
  simp [ffi.ByteArray.zeroes]

private theorem byteArray_ext_of_size_get
    {left right : ByteArray}
    (hSize : left.size = right.size)
    (hGet :
      ∀ (index : Nat)
        (hLeft : index < left.size)
        (hRight : index < right.size),
        left[index] = right[index]) :
    left = right := by
  apply ByteArray.ext
  apply Array.ext hSize
  intro index hLeft hRight
  rw [← ByteArray.getElem_eq_data_getElem left hLeft,
    ← ByteArray.getElem_eq_data_getElem right hRight]
  exact hGet index hLeft hRight

private theorem byteAt_eq_get
    (memory : ByteArray) (index : Nat)
    (hIndex : index < memory.size) :
    byteAt memory index = memory[index] := by
  rw [byteAt, Array.getD_eq_getD_getElem?]
  rw [show memory.data[index]? = some memory[index] by
    rw [Array.getElem?_eq_getElem hIndex]
    congr 1]
  rfl

theorem readWithPadding_writeWord_same
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hEnd : address + 32 ≤ machine.memory.size) :
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
          address 32 =
      value.toByteArray := by
  rw [readWithPadding_word_eq_extract]
  · apply ByteArray.ext
    simp only [ByteArray.extract, ByteArray.data_copySlice]
    simp only [ByteArray.empty, ByteArray.emptyWithCapacity,
      Nat.add_sub_cancel_left]
    simp only [Array.extract_empty_of_start_eq_stop,
      Array.empty_append]
    let suffix : Array UInt8 :=
      (#[] : Array UInt8).extract
        (0 + min 32
          ((machine.writeWord
            (EvmYul.UInt256.ofNat address) value).memory.data.size -
              address))
    change
      (machine.writeWord
          (EvmYul.UInt256.ofNat address) value).memory.data.extract
            address (address + 32) ++ suffix =
        value.toByteArray.data
    have hSuffix : suffix = #[] := by
      unfold suffix
      apply Array.extract_empty_of_size_le_start
      simp
    have hMiddle :
        (machine.writeWord
          (EvmYul.UInt256.ofNat address) value).memory.data.extract
            address (address + 32) =
          value.toByteArray.data := by
      rw [writeWord_memory_data value machine address hAddress hHost]
      have hAddressLe : address ≤ machine.memory.size := by omega
      have hPadding : address - machine.memory.size = 0 :=
        Nat.sub_eq_zero_of_le hAddressLe
      have hPrefix :
          (machine.memory.data.extract 0 address).size = address := by
        simp [Array.size_extract, Nat.min_eq_left hAddressLe]
      have hZero :
          (ffi.ByteArray.zeroes
            (OfNat.ofNat
              (address - machine.memory.size))).data = #[] := by
        rw [hPadding]
        rfl
      rw [hZero]
      simp only [Array.empty_append]
      rw [Array.extract_append_of_size_left_le_start hPrefix.le]
      simp only [hPrefix, Nat.sub_self,
        Nat.add_sub_cancel_left]
      rw [Array.extract_append_of_stop_le_size_left]
      · rw [← EvmYul.UInt256.size_toByteArray value]
        exact Array.extract_size
      · simp
    calc
      _ = value.toByteArray.data ++ suffix :=
        congrArg (fun bytes => bytes ++ suffix) hMiddle
      _ = value.toByteArray.data ++ #[] :=
        congrArg (fun bytes => value.toByteArray.data ++ bytes) hSuffix
      _ = value.toByteArray.data := Array.append_empty
  · rw [writeWord_memory_size_eq_of_end_le
      machine address value hAddress hHost hEnd]
    exact hEnd

theorem readWithPadding_writeWord_disjoint
    (machine : EvmYul.MachineState) (address query : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hWriteEnd : address + 32 ≤ machine.memory.size)
    (hReadEnd : query + 32 ≤ machine.memory.size)
    (hDisjoint :
      query + 32 ≤ address ∨ address + 32 ≤ query) :
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
          query 32 =
      machine.memory.readWithPadding query 32 := by
  have hMemorySize :=
    writeWord_memory_size_eq_of_end_le
      machine address value hAddress hHost hWriteEnd
  rw [readWithPadding_word_eq_extract,
    readWithPadding_word_eq_extract]
  · apply byteArray_ext_of_size_get
    · simp only [ByteArray.size_extract]
      rw [hMemorySize]
    · intro index hLeft hRight
      rw [ByteArray.get_extract hLeft,
        ByteArray.get_extract hRight]
      have hIndexLt : index < 32 := by
        simpa [Nat.min_eq_left hReadEnd] using hRight
      have hOriginal :
          query + index < machine.memory.size := by omega
      have hWritten :
          query + index <
            (machine.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.size := by
        rw [hMemorySize]
        exact hOriginal
      rw [← byteAt_eq_get _ _ hWritten,
        ← byteAt_eq_get _ _ hOriginal]
      apply
        byteAt_writeWord_of_outside
          value machine address (query + index)
          hAddress hHost
      rcases hDisjoint with hBefore | hAfter
      · left
        omega
      · right
        omega
  · exact hReadEnd
  · rw [hMemorySize]
    exact hReadEnd

theorem mstore_activeWords_eq_of_end_le
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hActive :
      address + 32 ≤ machine.activeWords.toNat * 32) :
    (machine.mstore
      (EvmYul.UInt256.ofNat address) value).activeWords =
        machine.activeWords := by
  have hWords :
      EvmYul.MachineState.M machine.activeWords.toNat address 32 =
        machine.activeWords.toNat := by
    simp only [EvmYul.MachineState.M]
    rw [max_eq_left]
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 32)]
    omega
  simp only [EvmYul.MachineState.mstore, hAddress]
  change
    EvmYul.UInt256.ofNat
        (EvmYul.MachineState.M
          machine.activeWords.toNat address 32) =
      machine.activeWords
  rw [hWords]
  exact EvmYul.UInt256.ofNat_toNat machine.activeWords

theorem lookupMemory_mstore_same
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hMemory : address + 32 ≤ machine.memory.size)
    (hActive :
      address + 32 ≤ machine.activeWords.toNat * 32)
    (hActiveNoWrap :
      machine.activeWords.toNat * 32 < EvmYul.UInt256.size) :
    (machine.mstore
        (EvmYul.UInt256.ofNat address) value).lookupMemory
          (EvmYul.UInt256.ofNat address) =
      value := by
  have hActiveEq :=
    mstore_activeWords_eq_of_end_le
      machine address value hAddress hActive
  have hMemoryEq :=
    writeWord_memory_size_eq_of_end_le
      machine address value hAddress hHost hMemory
  have hWords :
      EvmYul.MachineState.M machine.activeWords.toNat address 32 =
        machine.activeWords.toNat := by
    simp only [EvmYul.MachineState.M]
    rw [max_eq_left]
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 32)]
    omega
  unfold EvmYul.MachineState.lookupMemory
  simp only [EvmYul.MachineState.mstore, hAddress]
  rw [if_neg]
  · rw [readWithPadding_writeWord_same
      machine address value hAddress hHost hMemory]
    simp
  · simp only [not_or, not_le]
    constructor
    · simpa [hMemoryEq] using
        (show address < machine.memory.size by omega)
    · have hAddressLt : address < EvmYul.UInt256.size := by
        omega
      simp only [EvmYul.MachineState.writeWord,
        EvmYul.writeBytes]
      rw [hWords]
      intro hLe
      have hLeWord :
          machine.activeWords * (⟨32⟩ : EvmYul.UInt256) ≤
            EvmYul.UInt256.ofNat address := by
        simpa using hLe
      have hLeNat :
          (machine.activeWords *
            (⟨32⟩ : EvmYul.UInt256)).toNat ≤
            (EvmYul.UInt256.ofNat address).toNat :=
        hLeWord
      have hProduct :
          (machine.activeWords *
            (⟨32⟩ : EvmYul.UInt256)).toNat =
            (machine.activeWords.toNat * 32) %
              EvmYul.UInt256.size := by
        change
          (EvmYul.UInt256.mul machine.activeWords
            (⟨32⟩ : EvmYul.UInt256)).toNat =
              (machine.activeWords.toNat * 32) %
                EvmYul.UInt256.size
        unfold EvmYul.UInt256.mul EvmYul.UInt256.toNat
        rfl
      rw [hProduct,
        EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt] at hLeNat
      rw [Nat.mod_eq_of_lt hActiveNoWrap] at hLeNat
      omega

theorem lookupMemory_mstore_disjoint
    (machine : EvmYul.MachineState) (address query : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query)
    (hHost : address + 32 < USize.size)
    (hWriteMemory : address + 32 ≤ machine.memory.size)
    (hReadMemory : query + 32 ≤ machine.memory.size)
    (hWriteActive :
      address + 32 ≤ machine.activeWords.toNat * 32)
    (hDisjoint :
      query + 32 ≤ address ∨ address + 32 ≤ query) :
    (machine.mstore
        (EvmYul.UInt256.ofNat address) value).lookupMemory
          (EvmYul.UInt256.ofNat query) =
      machine.lookupMemory (EvmYul.UInt256.ofNat query) := by
  have hMemorySize :=
    writeWord_memory_size_eq_of_end_le
      machine address value hAddress hHost hWriteMemory
  have hActiveEq :=
    mstore_activeWords_eq_of_end_le
      machine address value hAddress hWriteActive
  unfold EvmYul.MachineState.lookupMemory
  rw [show
      (machine.mstore
        (EvmYul.UInt256.ofNat address) value).memory.size =
          machine.memory.size by
    simpa [EvmYul.MachineState.mstore] using hMemorySize]
  rw [hActiveEq]
  by_cases hGuard :
      (EvmYul.UInt256.ofNat query).toNat ≥ machine.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          machine.activeWords * (⟨32⟩ : EvmYul.UInt256)
  · rw [if_pos hGuard, if_pos hGuard]
  · rw [if_neg hGuard, if_neg hGuard]
    simp only [hQuery]
    change
      EvmYul.UInt256.ofNat
          (EvmYul.fromByteArrayBigEndian
            ((machine.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
                query 32)) =
        EvmYul.UInt256.ofNat
          (EvmYul.fromByteArrayBigEndian
            (machine.memory.readWithPadding query 32))
    rw [readWithPadding_writeWord_disjoint
      machine address query value hAddress hHost
      hWriteMemory hReadMemory hDisjoint]

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
