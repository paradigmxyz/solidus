import EvmCompiler.Core.MemoryContract
import EvmYul.MachineStateOps

namespace EvmCompiler
namespace Compiler
namespace MemoryRelation

theorem usize_size_lt_uint256_size :
    USize.size < EvmYul.UInt256.size := by
  rcases USize.size_eq with h | h <;>
    simp [h, EvmYul.UInt256.size]

theorem usize_size_add_31_lt_uint256_size :
    USize.size + 31 < EvmYul.UInt256.size := by
  rcases USize.size_eq with h | h <;>
    simp [h, EvmYul.UInt256.size]

def byteAt (memory : ByteArray) (address : Nat) : UInt8 :=
  memory.data.getD address 0

private theorem byteAt_copySlice_of_outside
    (source dest : ByteArray)
    (sourceAddress destAddress length query : Nat)
    (hDest : destAddress ≤ dest.size)
    (hSource : sourceAddress + length ≤ source.size)
    (hOutside :
      query < destAddress ∨ destAddress + length ≤ query) :
    byteAt
        (source.copySlice sourceAddress dest destAddress length) query =
      byteAt dest query := by
  rw [byteAt, ByteArray.data_copySlice, byteAt]
  let pre := dest.data.extract 0 destAddress
  let copied :=
    source.data.extract sourceAddress (sourceAddress + length)
  let post :=
    dest.data.extract (destAddress + length) dest.data.size
  have hSourceSub : length ≤ source.size - sourceAddress := by
    omega
  have hMin :
      min length (source.data.size - sourceAddress) = length := by
    rw [Nat.min_eq_left]
    simpa using hSourceSub
  rw [hMin]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  change
    (pre ++ copied ++ post)[query]?.getD 0 =
      dest.data[query]?.getD 0
  have hPreSize : pre.size = destAddress := by
    simp [pre, Array.size_extract, Nat.min_eq_left hDest]
  have hCopiedSize : copied.size = length := by
    simp [copied, Array.size_extract, hSource]
  rcases hOutside with hBefore | hAfter
  · have hPre : query < pre.size := by
      simpa [hPreSize] using hBefore
    have hPrefix : query < (pre ++ copied).size := by
      simp [hPreSize, hCopiedSize]
      omega
    rw [Array.getElem?_append_left hPrefix,
      Array.getElem?_append_left hPre]
    have hQueryDest : query < dest.data.size := by
      simpa using hBefore.trans_le hDest
    simp only [pre, Array.getElem?_extract]
    rw [show min destAddress dest.data.size = destAddress by
      rw [Nat.min_eq_left]
      simpa using hDest]
    simp only [Nat.sub_zero, Nat.zero_add]
    rw [if_pos hBefore]
  · have hPast :
        (pre ++ copied).size ≤ query := by
      simp [hPreSize, hCopiedSize, hAfter]
    rw [Array.getElem?_append_right hPast]
    by_cases hInsideDest : query < dest.size
    · have hPostInside :
          query - (pre ++ copied).size <
            dest.size - (destAddress + length) := by
        simp [hPreSize, hCopiedSize]
        omega
      have hPostIndex :
          destAddress + length +
              (query - (pre ++ copied).size) =
            query := by
        simp [hPreSize, hCopiedSize]
        omega
      simp only [post, Array.getElem?_extract]
      rw [show dest.data.size = dest.size by rfl, min_self]
      rw [if_pos hPostInside, hPostIndex]
    · have hPostPast :
          post.size ≤ query - (pre ++ copied).size := by
        simp [post, Array.size_extract, hPreSize, hCopiedSize]
        omega
      rw [Array.getElem?_eq_none hPostPast]
      rw [Array.getElem?_eq_none (by simpa using Nat.le_of_not_gt hInsideDest)]

private theorem byteAt_copySlice_of_inside
    (source dest : ByteArray)
    (sourceAddress destAddress length query : Nat)
    (hDest : destAddress ≤ dest.size)
    (hSource : sourceAddress + length ≤ source.size)
    (hStart : destAddress ≤ query)
    (hEnd : query < destAddress + length) :
    byteAt
        (source.copySlice sourceAddress dest destAddress length) query =
      byteAt source (sourceAddress + (query - destAddress)) := by
  rw [byteAt, ByteArray.data_copySlice, byteAt]
  let pre := dest.data.extract 0 destAddress
  let copied :=
    source.data.extract sourceAddress (sourceAddress + length)
  let post :=
    dest.data.extract (destAddress + length) dest.data.size
  have hSourceSub : length ≤ source.size - sourceAddress := by
    omega
  have hMin :
      min length (source.data.size - sourceAddress) = length := by
    rw [Nat.min_eq_left]
    simpa using hSourceSub
  rw [hMin]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  change
    (pre ++ copied ++ post)[query]?.getD 0 =
      source.data[sourceAddress + (query - destAddress)]?.getD 0
  have hPreSize : pre.size = destAddress := by
    simp [pre, Array.size_extract, Nat.min_eq_left hDest]
  have hCopiedSize : copied.size = length := by
    simp [copied, Array.size_extract, hSource]
  have hPastPre : pre.size ≤ query := by
    simpa [hPreSize] using hStart
  have hPrefixInside : query < (pre ++ copied).size := by
    simp [hPreSize, hCopiedSize]
    omega
  rw [Array.getElem?_append_left hPrefixInside,
    Array.getElem?_append_right hPastPre]
  have hInsideCopied :
      query - pre.size < copied.size := by
    simp [hPreSize, hCopiedSize]
    omega
  simp only [copied, Array.getElem?_extract]
  rw [show min (sourceAddress + length) source.data.size =
      sourceAddress + length by
    rw [Nat.min_eq_left]
    simpa using hSource]
  have hInsideLength : query - pre.size < length := by
    rw [← hCopiedSize]
    exact hInsideCopied
  rw [if_pos (by simpa [hPreSize] using hInsideLength)]
  congr 2
  simp [hPreSize]

private theorem size_copySlice_ge_dest
    (source dest : ByteArray)
    (sourceAddress destAddress length : Nat)
    (hDest : destAddress ≤ dest.size)
    (hSource : sourceAddress + length ≤ source.size) :
    dest.size ≤
      (source.copySlice sourceAddress dest destAddress length).size := by
  change
    dest.size ≤
      (source.copySlice
        sourceAddress dest destAddress length).data.size
  rw [ByteArray.data_copySlice]
  have hSourceSub : length ≤ source.size - sourceAddress := by
    omega
  have hMin :
      min length (source.data.size - sourceAddress) = length := by
    rw [Nat.min_eq_left]
    simpa using hSourceSub
  rw [hMin]
  have hPre :
      (dest.data.extract 0 destAddress).size = destAddress := by
    simp [Array.size_extract, Nat.min_eq_left hDest]
  have hCopied :
      (source.data.extract
        sourceAddress (sourceAddress + length)).size = length := by
    simp [Array.size_extract, hSource]
  have hPost :
      (dest.data.extract
        (destAddress + length) dest.data.size).size =
          dest.size - (destAddress + length) := by
    simp [Array.size_extract]
  simp only [Array.size_append]
  rw [hPre, hCopied, hPost]
  omega

private theorem byteAt_append_zeroes
    (dest : ByteArray) (padding : USize) (query : Nat) :
    byteAt (dest ++ ffi.ByteArray.zeroes padding) query =
      byteAt dest query := by
  unfold byteAt
  simp only [ByteArray.data_append]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  by_cases hInside : query < dest.data.size
  · rw [Array.getElem?_append_left hInside]
  · have hPast : dest.data.size ≤ query :=
      Nat.le_of_not_gt hInside
    rw [Array.getElem?_append_right hPast]
    rw [ffi.ByteArray.data_getElem?_zeroes]
    by_cases hPadding : query - dest.data.size < padding.toNat
    · rw [if_pos hPadding]
      rw [Array.getElem?_eq_none hPast]
      rfl
    · rw [if_neg hPadding]
      rw [Array.getElem?_eq_none hPast]

private theorem byteAt_of_size_le
    (memory : ByteArray) (query : Nat)
    (hPast : memory.size ≤ query) :
    byteAt memory query = 0 := by
  unfold byteAt
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_none (by simpa using hPast)]
  rfl

private theorem byteAt_zeroes
    (size : USize) (query : Nat) :
    byteAt (ffi.ByteArray.zeroes size) query = 0 := by
  unfold byteAt
  rw [Array.getD_eq_getD_getElem?]
  rw [ffi.ByteArray.data_getElem?_zeroes]
  split <;> rfl

set_option maxHeartbeats 1000000 in
theorem byteAt_write_of_outside
    (source dest : ByteArray)
    (sourceAddress destAddress length query : Nat)
    (hHost : destAddress + length < USize.size)
    (hOutside :
      query < destAddress ∨ destAddress + length ≤ query) :
    byteAt
        (source.write sourceAddress dest destAddress length) query =
      byteAt dest query := by
  unfold ByteArray.write
  split
  · rfl
  · rename_i hPositive
    split
    · rename_i hSourcePast
      let copiedLength := min length (dest.size - destAddress)
      let copiedAddress := min destAddress dest.size
      let zeroes :=
        ffi.ByteArray.zeroes (OfNat.ofNat copiedLength)
      have hCopiedLength : copiedLength < USize.size := by
        exact lt_of_le_of_lt
          (Nat.min_le_left _ _) (lt_of_le_of_lt
            (Nat.le_add_left length destAddress) hHost)
      have hZeroesSize : zeroes.size = copiedLength := by
        simp [zeroes, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hCopiedLength
      have hCopiedAddress : copiedAddress ≤ dest.size := by
        exact Nat.min_le_right _ _
      have hSourceBound : 0 + copiedLength ≤ zeroes.size := by
        simp [hZeroesSize]
      have hCopiedOutside :
          query < copiedAddress ∨
            copiedAddress + copiedLength ≤ query := by
        rcases hOutside with hBefore | hAfter
        · by_cases hQuery : query < dest.size
          · left
            simp [copiedAddress]
            exact ⟨hBefore, hQuery⟩
          · right
            have hAddressPast : dest.size ≤ destAddress := by
              by_contra hNot
              have hAddressInside : destAddress < dest.size :=
                Nat.lt_of_not_ge hNot
              exact hQuery (hBefore.trans hAddressInside)
            have hCopiedZero : copiedLength = 0 := by
              simp [copiedLength,
                Nat.sub_eq_zero_of_le hAddressPast]
            simp [copiedAddress, hCopiedZero,
              Nat.min_eq_right hAddressPast,
              Nat.le_of_not_gt hQuery]
        · right
          have hAddressLe : copiedAddress ≤ destAddress :=
            Nat.min_le_left _ _
          have hLengthLe : copiedLength ≤ length :=
            Nat.min_le_left _ _
          omega
      exact
        byteAt_copySlice_of_outside zeroes dest 0 copiedAddress
          copiedLength query hCopiedAddress hSourceBound hCopiedOutside
    · rename_i hSourceInside
      let practicalLength := min length (source.size - sourceAddress)
      let endPaddingAddress := min dest.size (destAddress + length)
      let sourcePaddingLength :=
        endPaddingAddress - (destAddress + practicalLength)
      let sourcePadding :=
        ffi.ByteArray.zeroes (OfNat.ofNat sourcePaddingLength)
      let destPaddingLength := destAddress - dest.size
      let destPadding :=
        ffi.ByteArray.zeroes (OfNat.ofNat destPaddingLength)
      let copiedSource := source ++ sourcePadding
      let copiedDest := dest ++ destPadding
      let copiedLength := practicalLength + sourcePaddingLength
      have hDestAddressLt : destAddress < USize.size := by
        omega
      have hDestPaddingLt : destPaddingLength < USize.size := by
        exact lt_of_le_of_lt
          (Nat.sub_le _ _) hDestAddressLt
      have hSourcePaddingLe : sourcePaddingLength ≤ length := by
        dsimp [sourcePaddingLength, endPaddingAddress, practicalLength]
        omega
      have hSourcePaddingLt : sourcePaddingLength < USize.size := by
        exact lt_of_le_of_lt hSourcePaddingLe
          (lt_of_le_of_lt
            (Nat.le_add_left length destAddress) hHost)
      have hDestPaddingSize :
          destPadding.size = destPaddingLength := by
        simp [destPadding, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hDestPaddingLt
      have hSourcePaddingSize :
          sourcePadding.size = sourcePaddingLength := by
        simp [sourcePadding, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hSourcePaddingLt
      have hPracticalBound :
          sourceAddress + practicalLength ≤ source.size := by
        dsimp [practicalLength]
        omega
      have hCopiedDestBound :
          destAddress ≤ copiedDest.size := by
        simp [copiedDest, hDestPaddingSize, destPaddingLength]
        omega
      have hCopiedSourceBound :
          sourceAddress + copiedLength ≤ copiedSource.size := by
        simp [copiedLength, copiedSource, hSourcePaddingSize]
        omega
      have hCopiedLengthLe : copiedLength ≤ length := by
        dsimp [copiedLength, sourcePaddingLength,
          endPaddingAddress, practicalLength]
        omega
      have hCopiedOutside :
          query < destAddress ∨
            destAddress + copiedLength ≤ query := by
        rcases hOutside with hBefore | hAfter
        · exact Or.inl hBefore
        · exact Or.inr
            ((Nat.add_le_add_left hCopiedLengthLe destAddress).trans hAfter)
      exact
        (byteAt_copySlice_of_outside copiedSource copiedDest
          sourceAddress destAddress copiedLength query
          hCopiedDestBound hCopiedSourceBound hCopiedOutside).trans
          (byteAt_append_zeroes dest
            (OfNat.ofNat destPaddingLength) query)

set_option maxHeartbeats 1000000 in
theorem byteAt_write_of_inside
    (source dest : ByteArray)
    (sourceAddress destAddress length query : Nat)
    (hHost : destAddress + length < USize.size)
    (hStart : destAddress ≤ query)
    (hEnd : query < destAddress + length) :
    byteAt
        (source.write sourceAddress dest destAddress length) query =
      byteAt source (sourceAddress + (query - destAddress)) := by
  unfold ByteArray.write
  split
  · omega
  · rename_i hPositive
    split
    · rename_i hSourcePast
      let copiedLength := min length (dest.size - destAddress)
      let copiedAddress := min destAddress dest.size
      let zeroes :=
        ffi.ByteArray.zeroes (OfNat.ofNat copiedLength)
      have hCopiedLength : copiedLength < USize.size := by
        exact lt_of_le_of_lt
          (Nat.min_le_left _ _) (lt_of_le_of_lt
            (Nat.le_add_left length destAddress) hHost)
      have hZeroesSize : zeroes.size = copiedLength := by
        simp [zeroes, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hCopiedLength
      have hCopiedAddress : copiedAddress ≤ dest.size :=
        Nat.min_le_right _ _
      have hSourceBound : 0 + copiedLength ≤ zeroes.size := by
        simp [hZeroesSize]
      by_cases hCopied : query < copiedAddress + copiedLength
      · have hCopiedStart : copiedAddress ≤ query := by
          dsimp [copiedAddress]
          omega
        calc
          byteAt
              (zeroes.copySlice 0 dest copiedAddress copiedLength)
              query =
            byteAt zeroes (0 + (query - copiedAddress)) :=
              byteAt_copySlice_of_inside zeroes dest 0 copiedAddress
                copiedLength query hCopiedAddress hSourceBound
                hCopiedStart hCopied
          _ = 0 := byteAt_zeroes _ _
          _ =
            byteAt source
              (sourceAddress + (query - destAddress)) := by
                symm
                apply byteAt_of_size_le
                exact hSourcePast.trans
                  (Nat.le_add_right sourceAddress
                    (query - destAddress))
      · have hCopiedOutside :
            query < copiedAddress ∨
              copiedAddress + copiedLength ≤ query := by
          exact Or.inr (Nat.le_of_not_gt hCopied)
        have hDestPast : dest.size ≤ query := by
          dsimp [copiedAddress, copiedLength] at hCopied
          by_cases hAddress : destAddress ≤ dest.size
          · rw [Nat.min_eq_left hAddress] at hCopied
            by_cases hFits : length ≤ dest.size - destAddress
            · rw [Nat.min_eq_left hFits] at hCopied
              omega
            · rw [Nat.min_eq_right (Nat.le_of_not_ge hFits)] at hCopied
              omega
          · have hAddressPast := Nat.le_of_not_ge hAddress
            rw [Nat.min_eq_right hAddressPast,
              Nat.sub_eq_zero_of_le hAddressPast] at hCopied
            omega
        calc
          byteAt
              (zeroes.copySlice 0 dest copiedAddress copiedLength)
              query =
            byteAt dest query :=
              byteAt_copySlice_of_outside zeroes dest 0 copiedAddress
                copiedLength query hCopiedAddress hSourceBound
                hCopiedOutside
          _ = 0 := byteAt_of_size_le dest query hDestPast
          _ =
            byteAt source
              (sourceAddress + (query - destAddress)) := by
                symm
                apply byteAt_of_size_le
                exact hSourcePast.trans
                  (Nat.le_add_right sourceAddress
                    (query - destAddress))
    · rename_i hSourceInside
      let practicalLength := min length (source.size - sourceAddress)
      let endPaddingAddress := min dest.size (destAddress + length)
      let sourcePaddingLength :=
        endPaddingAddress - (destAddress + practicalLength)
      let sourcePadding :=
        ffi.ByteArray.zeroes (OfNat.ofNat sourcePaddingLength)
      let destPaddingLength := destAddress - dest.size
      let destPadding :=
        ffi.ByteArray.zeroes (OfNat.ofNat destPaddingLength)
      let copiedSource := source ++ sourcePadding
      let copiedDest := dest ++ destPadding
      let copiedLength := practicalLength + sourcePaddingLength
      have hDestAddressLt : destAddress < USize.size := by
        omega
      have hDestPaddingLt : destPaddingLength < USize.size := by
        exact lt_of_le_of_lt
          (Nat.sub_le _ _) hDestAddressLt
      have hSourcePaddingLe : sourcePaddingLength ≤ length := by
        dsimp [sourcePaddingLength, endPaddingAddress, practicalLength]
        omega
      have hSourcePaddingLt : sourcePaddingLength < USize.size := by
        exact lt_of_le_of_lt hSourcePaddingLe
          (lt_of_le_of_lt
            (Nat.le_add_left length destAddress) hHost)
      have hDestPaddingSize :
          destPadding.size = destPaddingLength := by
        simp [destPadding, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hDestPaddingLt
      have hSourcePaddingSize :
          sourcePadding.size = sourcePaddingLength := by
        simp [sourcePadding, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hSourcePaddingLt
      have hPracticalBound :
          sourceAddress + practicalLength ≤ source.size := by
        dsimp [practicalLength]
        omega
      have hCopiedDestBound :
          destAddress ≤ copiedDest.size := by
        simp [copiedDest, hDestPaddingSize, destPaddingLength]
        omega
      have hCopiedSourceBound :
          sourceAddress + copiedLength ≤ copiedSource.size := by
        simp [copiedLength, copiedSource, hSourcePaddingSize]
        omega
      by_cases hCopied : query < destAddress + copiedLength
      · calc
          byteAt
              (copiedSource.copySlice sourceAddress copiedDest
                destAddress copiedLength) query =
            byteAt copiedSource
              (sourceAddress + (query - destAddress)) :=
              byteAt_copySlice_of_inside copiedSource copiedDest
                sourceAddress destAddress copiedLength query
                hCopiedDestBound hCopiedSourceBound hStart hCopied
          _ =
            byteAt source
              (sourceAddress + (query - destAddress)) :=
              byteAt_append_zeroes source
                (OfNat.ofNat sourcePaddingLength)
                (sourceAddress + (query - destAddress))
      · have hCopiedOutside :
            query < destAddress ∨
              destAddress + copiedLength ≤ query :=
          Or.inr (Nat.le_of_not_gt hCopied)
        have hSourcePast :
            source.size ≤ sourceAddress + (query - destAddress) := by
          dsimp [copiedLength, practicalLength,
            sourcePaddingLength, endPaddingAddress] at hCopied
          by_cases hFits : length ≤ source.size - sourceAddress
          · rw [Nat.min_eq_left hFits] at hCopied
            omega
          · rw [Nat.min_eq_right (Nat.le_of_not_ge hFits)] at hCopied
            omega
        have hDestPast : dest.size ≤ query := by
          dsimp [copiedLength, practicalLength,
            sourcePaddingLength, endPaddingAddress] at hCopied
          omega
        calc
          byteAt
              (copiedSource.copySlice sourceAddress copiedDest
                destAddress copiedLength) query =
            byteAt copiedDest query :=
              byteAt_copySlice_of_outside copiedSource copiedDest
                sourceAddress destAddress copiedLength query
                hCopiedDestBound hCopiedSourceBound hCopiedOutside
          _ = byteAt dest query :=
            byteAt_append_zeroes dest
              (OfNat.ofNat destPaddingLength) query
          _ = 0 := byteAt_of_size_le dest query hDestPast
          _ =
            byteAt source
              (sourceAddress + (query - destAddress)) := by
                symm
                exact byteAt_of_size_le source _ hSourcePast

set_option maxHeartbeats 1000000 in
theorem size_write_ge
    (source dest : ByteArray)
    (sourceAddress destAddress length : Nat)
    (hHost : destAddress + length < USize.size) :
    dest.size ≤
      (source.write sourceAddress dest destAddress length).size := by
  unfold ByteArray.write
  split
  · simp
  · split
    · let copiedLength := min length (dest.size - destAddress)
      let copiedAddress := min destAddress dest.size
      let zeroes :=
        ffi.ByteArray.zeroes (OfNat.ofNat copiedLength)
      have hCopiedLength : copiedLength < USize.size := by
        exact lt_of_le_of_lt
          (Nat.min_le_left _ _) (lt_of_le_of_lt
            (Nat.le_add_left length destAddress) hHost)
      have hZeroesSize : zeroes.size = copiedLength := by
        simp [zeroes, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hCopiedLength
      exact
        size_copySlice_ge_dest zeroes dest 0 copiedAddress
          copiedLength (Nat.min_le_right _ _)
          (by simp [hZeroesSize])
    · let practicalLength := min length (source.size - sourceAddress)
      let endPaddingAddress := min dest.size (destAddress + length)
      let sourcePaddingLength :=
        endPaddingAddress - (destAddress + practicalLength)
      let sourcePadding :=
        ffi.ByteArray.zeroes (OfNat.ofNat sourcePaddingLength)
      let destPaddingLength := destAddress - dest.size
      let destPadding :=
        ffi.ByteArray.zeroes (OfNat.ofNat destPaddingLength)
      let copiedSource := source ++ sourcePadding
      let copiedDest := dest ++ destPadding
      let copiedLength := practicalLength + sourcePaddingLength
      have hDestAddressLt : destAddress < USize.size := by
        omega
      have hDestPaddingLt : destPaddingLength < USize.size := by
        exact lt_of_le_of_lt
          (Nat.sub_le _ _) hDestAddressLt
      have hSourcePaddingLe : sourcePaddingLength ≤ length := by
        dsimp [sourcePaddingLength, endPaddingAddress, practicalLength]
        omega
      have hSourcePaddingLt : sourcePaddingLength < USize.size := by
        exact lt_of_le_of_lt hSourcePaddingLe
          (lt_of_le_of_lt
            (Nat.le_add_left length destAddress) hHost)
      have hDestPaddingSize :
          destPadding.size = destPaddingLength := by
        simp [destPadding, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hDestPaddingLt
      have hSourcePaddingSize :
          sourcePadding.size = sourcePaddingLength := by
        simp [sourcePadding, ffi.ByteArray.size_zeroes]
        exact USize.toNat_ofNat_of_lt' hSourcePaddingLt
      have hPracticalBound :
          sourceAddress + practicalLength ≤ source.size := by
        dsimp [practicalLength]
        omega
      have hCopiedDestBound :
          destAddress ≤ copiedDest.size := by
        simp [copiedDest, hDestPaddingSize, destPaddingLength]
        omega
      have hCopiedSourceBound :
          sourceAddress + copiedLength ≤ copiedSource.size := by
        simp [copiedLength, copiedSource, hSourcePaddingSize]
        omega
      have hDestLe : dest.size ≤ copiedDest.size := by
        simp [copiedDest]
      exact hDestLe.trans
        (size_copySlice_ge_dest copiedSource copiedDest
          sourceAddress destAddress copiedLength
          hCopiedDestBound hCopiedSourceBound)

set_option maxHeartbeats 1000000 in
theorem writeBytes_memory_data
    (bytes : ByteArray) (machine : EvmYul.MachineState)
    (address length : Nat)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size) :
    (EvmYul.writeBytes bytes 0 machine address length).memory.data =
      machine.memory.data.extract 0 address ++
        ((ffi.ByteArray.zeroes
            (OfNat.ofNat (address - machine.memory.size))).data ++
          (bytes.data ++
            machine.memory.data.extract
              (address + length) machine.memory.size)) := by
  unfold EvmYul.writeBytes ByteArray.write
  rw [if_neg (Nat.ne_of_gt hPositive)]
  have hSource : ¬0 ≥ bytes.size := by
    rw [hLength]
    omega
  rw [if_neg hSource]
  simp only [Nat.sub_zero, hLength, Nat.min_self, Nat.add_zero,
    Nat.sub_self]
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
  have hBytes :
      bytes.data.extract 0 length = bytes.data := by
    rw [← hLength]
    exact Array.extract_size
  have hMemorySuffix :
      machine.memory.data.extract (address + length)
          (machine.memory.size + (address - machine.memory.size)) =
        machine.memory.data.extract (address + length)
          machine.memory.size := by
    by_cases hStart : machine.memory.size ≤ address + length
    · rw [Array.extract_empty_of_size_le_start hStart,
        Array.extract_empty_of_size_le_start hStart]
    · have hAddressLe : address ≤ machine.memory.size := by omega
      simp [Nat.sub_eq_zero_of_le hAddressLe]
  have hZeroSuffix :
      (ffi.ByteArray.zeroes
          (OfNat.ofNat (address - machine.memory.size))).data.extract
            (address + length - machine.memory.size)
            (address - machine.memory.size) =
        #[] := by
    apply Array.extract_empty_of_size_le_start
    rw [hZeroSize]
    omega
  rw [hLength]
  simp only [Nat.min_self, Nat.sub_self]
  rw [hZeroPrefix, hBytes, hMemorySuffix, hZeroSuffix]
  simp

theorem byteAt_writeBytes_of_outside
    (bytes : ByteArray) (machine : EvmYul.MachineState)
    (address length query : Nat)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size)
    (hOutside : query < address ∨ address + length ≤ query) :
    byteAt
        (EvmYul.writeBytes bytes 0 machine address length).memory query =
      byteAt machine.memory query := by
  rw [byteAt,
    writeBytes_memory_data bytes machine address length
      hLength hPositive hHost,
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
  let sourceBytes := bytes.data
  let post :=
    machine.memory.data.extract (address + length) machine.memory.size
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  change
    (pre ++ (pad ++ (sourceBytes ++ post)))[query]?.getD 0 =
      machine.memory.data[query]?.getD 0
  have hPrefixSize :
      pre.size = min address machine.memory.size := by
    simp [pre, Array.size_extract]
  have hPaddingSize :
      pad.size = address - machine.memory.size := by
    simp [pad, ffi.ByteArray.size_zeroes, hPadding]
  have hBytesSize : sourceBytes.size = length := by
    simpa [sourceBytes] using hLength
  have hSuffixSize :
      post.size = machine.memory.size - (address + length) := by
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
      have hPastBytes :
          sourceBytes.size ≤ query - pre.size - pad.size := by
        rw [hBytesSize, hPrefixSize, hPaddingSize, hMin, hPad]
        omega
      rw [Array.getElem?_append_right hPastBytes]
      have hPostInside :
          query - address - length <
            machine.memory.size - (address + length) := by
        omega
      have hPostIndex :
          address + length + (query - address - length) = query := by
        omega
      rw [show
        post[query - pre.size - pad.size - sourceBytes.size]? =
          machine.memory.data[query]? by
        simp only [post, Array.getElem?_extract, hPrefixSize,
          hPaddingSize, hBytesSize, hMin, hPad]
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
        have hPastBytes :
            sourceBytes.size ≤ query - pre.size - pad.size := by
          rw [hBytesSize, hPrefixSize, hPaddingSize, hMin, hPad]
          omega
        rw [Array.getElem?_append_right hPastBytes]
        have hPastSuffix :
            post.size ≤
              query - pre.size - pad.size - sourceBytes.size := by
          rw [hSuffixSize, hPrefixSize, hPaddingSize, hBytesSize,
            hMin, hPad]
          omega
        rw [show
          post[query - pre.size - pad.size - sourceBytes.size]? =
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
        have hPastBytes :
            sourceBytes.size ≤ query - pre.size - pad.size := by
          rw [hBytesSize, hPrefixSize, hPaddingSize, hMin]
          omega
        rw [Array.getElem?_append_right hPastBytes]
        have hSuffixEmpty : post = #[] := by
          apply Array.extract_empty_of_size_le_start
          change machine.memory.size ≤ address + length
          omega
        simp [hSuffixEmpty, hMemory]

theorem byteAt_writeBytes_of_inside
    (bytes : ByteArray) (machine : EvmYul.MachineState)
    (address length query : Nat)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size)
    (hStart : address ≤ query)
    (hEnd : query < address + length) :
    byteAt
        (EvmYul.writeBytes bytes 0 machine address length).memory query =
      byteAt bytes (query - address) := by
  rw [byteAt,
    writeBytes_memory_data bytes machine address length
      hLength hPositive hHost,
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
  let post :=
    machine.memory.data.extract (address + length) machine.memory.size
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  change
    (pre ++ (pad ++ (bytes.data ++ post)))[query]?.getD 0 =
      bytes.data[query - address]?.getD 0
  have hPrefixSize :
      pre.size = min address machine.memory.size := by
    simp [pre, Array.size_extract]
  have hPaddingSize :
      pad.size = address - machine.memory.size := by
    simp [pad, ffi.ByteArray.size_zeroes, hPadding]
  have hPrefixPaddingSize :
      (pre ++ pad).size = address := by
    simp only [Array.size_append, hPrefixSize, hPaddingSize]
    omega
  rw [← Array.append_assoc]
  have hPastPrefix : (pre ++ pad).size ≤ query := by
    rw [hPrefixPaddingSize]
    exact hStart
  rw [Array.getElem?_append_right hPastPrefix]
  have hInsideBytes :
      query - (pre ++ pad).size < bytes.data.size := by
    rw [hPrefixPaddingSize]
    simpa [hLength] using (show query - address < length by omega)
  rw [Array.getElem?_append_left hInsideBytes]
  rw [hPrefixPaddingSize]

theorem writeBytes_memory_size_ge
    (bytes : ByteArray) (machine : EvmYul.MachineState)
    (address length : Nat)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size) :
    machine.memory.size ≤
      (EvmYul.writeBytes bytes 0 machine address length).memory.size := by
  change
    machine.memory.data.size ≤
      (EvmYul.writeBytes bytes 0 machine address length).memory.data.size
  rw [writeBytes_memory_data bytes machine address length
    hLength hPositive hHost]
  have hPrefix :
      (machine.memory.data.extract 0 address).size =
        min address machine.memory.size := by
    simp [Array.size_extract]
  have hPadding :
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).data.size =
        address - machine.memory.size := by
    change
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).size =
        address - machine.memory.size
    rw [ffi.ByteArray.size_zeroes]
    apply USize.toNat_ofNat_of_lt'
    omega
  have hSuffix :
      (machine.memory.data.extract
        (address + length) machine.memory.size).size =
          machine.memory.size - (address + length) := by
    simp [Array.size_extract]
  have hBytes : bytes.data.size = length := by
    exact hLength
  have hMemory :
      machine.memory.data.size = machine.memory.size := by
    rfl
  simp only [Array.size_append]
  rw [hMemory, hPrefix, hPadding, hBytes, hSuffix]
  omega

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

theorem writeWord_memory_size_ge_end
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size) :
    address + 32 ≤
      (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.size := by
  change
    address + 32 ≤
      (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.data.size
  rw [writeWord_memory_data value machine address hAddress hHost]
  have hPrefix :
      (machine.memory.data.extract 0 address).size =
        min address machine.memory.size := by
    simp [Array.size_extract]
  have hPadding :
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).data.size =
        address - machine.memory.size := by
    change
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).size =
        address - machine.memory.size
    rw [ffi.ByteArray.size_zeroes]
    apply USize.toNat_ofNat_of_lt'
    omega
  have hWord : value.toByteArray.data.size = 32 :=
    EvmYul.UInt256.size_toByteArray value
  simp only [Array.size_append]
  rw [hPrefix, hPadding, hWord]
  omega

theorem writeWord_memory_size_ge
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size) :
    machine.memory.size ≤
      (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.size := by
  change
    machine.memory.size ≤
      (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.data.size
  rw [writeWord_memory_data value machine address hAddress hHost]
  have hPrefix :
      (machine.memory.data.extract 0 address).size =
        min address machine.memory.size := by
    simp [Array.size_extract]
  have hPadding :
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).data.size =
        address - machine.memory.size := by
    change
      (ffi.ByteArray.zeroes
        (OfNat.ofNat
          (address - machine.memory.size))).size =
        address - machine.memory.size
    rw [ffi.ByteArray.size_zeroes]
    apply USize.toNat_ofNat_of_lt'
    omega
  have hWord : value.toByteArray.data.size = 32 :=
    EvmYul.UInt256.size_toByteArray value
  have hPost :
      (machine.memory.data.extract
        (address + 32) machine.memory.size).size =
          machine.memory.size - (address + 32) := by
    simp [Array.size_extract]
  simp only [Array.size_append]
  rw [hPrefix, hPadding, hWord, hPost]
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

theorem readWithPadding_writeWord_same_growing
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size) :
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
          address 32 =
      value.toByteArray := by
  have hEnd :=
    writeWord_memory_size_ge_end
      machine address value hAddress hHost
  rw [readWithPadding_word_eq_extract _ _ hEnd]
  apply ByteArray.ext
  simp only [ByteArray.extract, ByteArray.data_copySlice]
  simp only [ByteArray.empty, ByteArray.emptyWithCapacity,
    Nat.add_sub_cancel_left]
  simp only [Array.extract_empty_of_start_eq_stop,
    Array.empty_append]
  let pre := machine.memory.data.extract 0 address
  let pad :=
    (ffi.ByteArray.zeroes
      (OfNat.ofNat (address - machine.memory.size))).data
  let bytes := value.toByteArray.data
  let post :=
    machine.memory.data.extract (address + 32) machine.memory.size
  have hData :=
    writeWord_memory_data value machine address hAddress hHost
  change
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.data.extract
          address (address + 32) ++
        (#[] : Array UInt8).extract
          (0 + min 32
            ((machine.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.data.size -
                address)) =
      bytes
  have hSuffix :
      (#[] : Array UInt8).extract
          (0 + min 32
            ((machine.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.data.size -
                address)) =
        #[] := by
    apply Array.extract_empty_of_size_le_start
    simp
  rw [hSuffix, Array.append_empty, hData]
  change
    (pre ++ (pad ++ (bytes ++ post))).extract
        address (address + 32) =
      bytes
  have hPrefixSize :
      (pre ++ pad).size = address := by
    have hPre :
        pre.size = min address machine.memory.size := by
      simp [pre, Array.size_extract]
    have hPad :
        pad.size = address - machine.memory.size := by
      change
        (ffi.ByteArray.zeroes
          (OfNat.ofNat
            (address - machine.memory.size))).size =
          address - machine.memory.size
      rw [ffi.ByteArray.size_zeroes]
      apply USize.toNat_ofNat_of_lt'
      omega
    simp only [Array.size_append, hPre, hPad]
    omega
  have hBytesSize : bytes.size = 32 := by
    simp [bytes]
  rw [← Array.append_assoc]
  rw [Array.extract_append_of_size_left_le_start hPrefixSize.le]
  simp only [hPrefixSize, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [Array.extract_append_of_stop_le_size_left]
  · rw [← hBytesSize]
    exact Array.extract_size
  · simpa [hBytesSize]

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

theorem mload_eq_lookup_of_end_le
    (machine : EvmYul.MachineState) (address : Nat)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hActive :
      address + 32 ≤ machine.activeWords.toNat * 32) :
    machine.mload (EvmYul.UInt256.ofNat address) =
      (machine.lookupMemory (EvmYul.UInt256.ofNat address), machine) := by
  have hWords :
      EvmYul.MachineState.M machine.activeWords.toNat address 32 =
        machine.activeWords.toNat := by
    simp only [EvmYul.MachineState.M]
    rw [max_eq_left]
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 32)]
    omega
  simp [EvmYul.MachineState.mload, hAddress, hWords,
    EvmYul.UInt256.ofNat_toNat]

theorem mstore_end_le_activeBytes
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hEnd : address + 32 < EvmYul.UInt256.size) :
    address + 32 ≤
      (machine.mstore
          (EvmYul.UInt256.ofNat address) value).activeWords.toNat * 32 := by
  have hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address :=
    EvmYul.UInt256.toNat_ofNat_of_lt
      (lt_of_le_of_lt (Nat.le_add_right address _) hEnd)
  have hM :
      EvmYul.MachineState.M machine.activeWords.toNat address 32 <
        EvmYul.UInt256.size := by
    simp only [EvmYul.MachineState.M]
    exact Nat.max_lt.mpr
      ⟨machine.activeWords.val.isLt,
        lt_of_le_of_lt (by omega) hEnd⟩
  simp only [EvmYul.MachineState.mstore, hAddress]
  change
    address + 32 ≤
      (EvmYul.UInt256.ofNat
        (EvmYul.MachineState.M machine.activeWords.toNat address 32)).toNat *
        32
  rw [EvmYul.UInt256.toNat_ofNat_of_lt hM]
  simp only [EvmYul.MachineState.M]
  omega

theorem mstore_activeBytes_lt_size_of_activeBytes_lt_size
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hActive :
      machine.activeWords.toNat * 32 < EvmYul.UInt256.size)
    (hHost : address + 32 < USize.size) :
    (machine.mstore
        (EvmYul.UInt256.ofNat address) value).activeWords.toNat * 32 <
      EvmYul.UInt256.size := by
  have hAddressLt : address < EvmYul.UInt256.size := by
    have hSize := usize_size_lt_uint256_size
    omega
  have hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address :=
    EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
  have hCeil :
      ((address + 32 + 31) / 32) * 32 <
        EvmYul.UInt256.size := by
    have hPlatform :
        USize.size + 31 < EvmYul.UInt256.size :=
      usize_size_add_31_lt_uint256_size
    have hDiv :=
      Nat.div_mul_le_self (address + 32 + 31) 32
    omega
  have hM :
      EvmYul.MachineState.M machine.activeWords.toNat address 32 <
        EvmYul.UInt256.size := by
    simp only [EvmYul.MachineState.M]
    exact Nat.max_lt.mpr
      ⟨machine.activeWords.val.isLt,
        lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by decide)) hCeil⟩
  have hToNat :
      (machine.mstore
          (EvmYul.UInt256.ofNat address) value).activeWords.toNat =
        EvmYul.MachineState.M machine.activeWords.toNat address 32 := by
    simp only [EvmYul.MachineState.mstore, hAddress]
    exact EvmYul.UInt256.toNat_ofNat_of_lt hM
  rw [hToNat]
  simp only [EvmYul.MachineState.M]
  by_cases hOrder :
      machine.activeWords.toNat ≤ (address + 32 + 31) / 32
  · rw [max_eq_right hOrder]
    exact hCeil
  · rw [max_eq_left (Nat.le_of_not_ge hOrder)]
    exact hActive

theorem lookupMemory_mstore_same_growing
    (machine : EvmYul.MachineState) (address : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hEnd : address + 32 < EvmYul.UInt256.size)
    (hActiveNoWrap :
      (machine.mstore
          (EvmYul.UInt256.ofNat address) value).activeWords.toNat * 32 <
        EvmYul.UInt256.size) :
    (machine.mstore
        (EvmYul.UInt256.ofNat address) value).lookupMemory
          (EvmYul.UInt256.ofNat address) =
      value := by
  let written :=
    machine.mstore (EvmYul.UInt256.ofNat address) value
  have hMemory :
      address + 32 ≤ written.memory.size := by
    simpa [written, EvmYul.MachineState.mstore] using
      (writeWord_memory_size_ge_end
        machine address value hAddress hHost)
  have hActive :
      address + 32 ≤ written.activeWords.toNat * 32 := by
    simpa [written] using
      (mstore_end_le_activeBytes machine address value hEnd)
  have hAddressLt : address < EvmYul.UInt256.size := by
    omega
  have hProduct :
      (written.activeWords * (⟨32⟩ : EvmYul.UInt256)).toNat =
        (written.activeWords.toNat * 32) %
          EvmYul.UInt256.size := by
    change
      (EvmYul.UInt256.mul written.activeWords
        (⟨32⟩ : EvmYul.UInt256)).toNat =
          (written.activeWords.toNat * 32) %
            EvmYul.UInt256.size
    unfold EvmYul.UInt256.mul EvmYul.UInt256.toNat
    rfl
  have hProductNoWrap :
      (written.activeWords * (⟨32⟩ : EvmYul.UInt256)).toNat =
        written.activeWords.toNat * 32 := by
    rw [hProduct, Nat.mod_eq_of_lt hActiveNoWrap]
  unfold EvmYul.MachineState.lookupMemory
  rw [if_neg]
  · simp only [EvmYul.MachineState.mstore, hAddress]
    change
      EvmYul.UInt256.ofNat
          (EvmYul.fromByteArrayBigEndian
            ((machine.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
                address 32)) =
        value
    rw [readWithPadding_writeWord_same_growing
      machine address value hAddress hHost]
    simp
  · simp only [not_or, not_le]
    constructor
    · simpa [written, hAddress] using
        (show address < written.memory.size by omega)
    · intro hLe
      have hLeNat :
          (written.activeWords *
              (⟨32⟩ : EvmYul.UInt256)).toNat ≤
            (EvmYul.UInt256.ofNat address).toNat :=
        hLe
      rw [hProductNoWrap,
        EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt] at hLeNat
      omega

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

theorem readWithPadding_writeWord_disjoint_growing
    (machine : EvmYul.MachineState) (address query : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + 32 < USize.size)
    (hReadEnd : query + 32 ≤ machine.memory.size)
    (hDisjoint :
      query + 32 ≤ address ∨ address + 32 ≤ query) :
    (machine.writeWord
        (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
          query 32 =
      machine.memory.readWithPadding query 32 := by
  have hSizeGe :=
    writeWord_memory_size_ge
      machine address value hAddress hHost
  have hWrittenEnd :
      query + 32 ≤
        (machine.writeWord
          (EvmYul.UInt256.ofNat address) value).memory.size :=
    hReadEnd.trans hSizeGe
  rw [readWithPadding_word_eq_extract _ _ hWrittenEnd,
    readWithPadding_word_eq_extract _ _ hReadEnd]
  apply byteArray_ext_of_size_get
  · simp [ByteArray.size_extract, hWrittenEnd, hReadEnd]
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
            (EvmYul.UInt256.ofNat address) value).memory.size :=
      lt_of_lt_of_le hOriginal hSizeGe
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

theorem readWithPadding_write_disjoint_growing
    (source : ByteArray) (machine : EvmYul.MachineState)
    (sourceAddress address length query : Nat)
    (hHost : address + length < USize.size)
    (hReadEnd : query + MemoryContract.wordBytes ≤ machine.memory.size)
    (hDisjoint :
      query + MemoryContract.wordBytes ≤ address ∨
        address + length ≤ query) :
    (source.write sourceAddress machine.memory address length).readWithPadding
          query MemoryContract.wordBytes =
      machine.memory.readWithPadding query MemoryContract.wordBytes := by
  have hSizeGe :=
    size_write_ge source machine.memory sourceAddress address length hHost
  have hWrittenEnd :
      query + MemoryContract.wordBytes ≤
        (source.write
          sourceAddress machine.memory address length).size :=
    hReadEnd.trans hSizeGe
  have hReadEnd32 : query + 32 ≤ machine.memory.size := by
    simpa [MemoryContract.wordBytes] using hReadEnd
  have hWrittenEnd32 :
      query + 32 ≤
        (source.write sourceAddress machine.memory address length).size := by
    simpa [MemoryContract.wordBytes] using hWrittenEnd
  change
    (source.write sourceAddress machine.memory address length).readWithPadding
          query 32 =
      machine.memory.readWithPadding query 32
  rw [readWithPadding_word_eq_extract _ _ hWrittenEnd32,
    readWithPadding_word_eq_extract _ _ hReadEnd32]
  apply byteArray_ext_of_size_get
  · simp [ByteArray.size_extract, hWrittenEnd32, hReadEnd32]
  · intro index hLeft hRight
    rw [ByteArray.get_extract hLeft,
      ByteArray.get_extract hRight]
    have hIndexLt : index < MemoryContract.wordBytes := by
      simpa [MemoryContract.wordBytes,
        Nat.min_eq_left hReadEnd32] using hRight
    have hOriginal :
        query + index < machine.memory.size := by
      omega
    have hWritten :
        query + index <
          (source.write sourceAddress machine.memory address length).size :=
      lt_of_lt_of_le hOriginal hSizeGe
    rw [← byteAt_eq_get _ _ hWritten,
      ← byteAt_eq_get _ _ hOriginal]
    apply
      byteAt_write_of_outside
        source machine.memory sourceAddress address length
          (query + index) hHost
    rcases hDisjoint with hBefore | hAfter
    · left
      omega
    · right
      omega

theorem readWithPadding_writeBytes_disjoint_growing
    (bytes : ByteArray) (machine : EvmYul.MachineState)
    (address length query : Nat)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size)
    (hReadEnd : query + MemoryContract.wordBytes ≤ machine.memory.size)
    (hDisjoint :
      query + MemoryContract.wordBytes ≤ address ∨
        address + length ≤ query) :
    (EvmYul.writeBytes bytes 0 machine address length).memory.readWithPadding
          query MemoryContract.wordBytes =
      machine.memory.readWithPadding query MemoryContract.wordBytes := by
  have hSizeGe :=
    writeBytes_memory_size_ge bytes machine address length
      hLength hPositive hHost
  have hWrittenEnd :
      query + MemoryContract.wordBytes ≤
        (EvmYul.writeBytes bytes 0 machine address length).memory.size :=
    hReadEnd.trans hSizeGe
  have hReadEnd32 : query + 32 ≤ machine.memory.size := by
    simpa [MemoryContract.wordBytes] using hReadEnd
  have hWrittenEnd32 :
      query + 32 ≤
        (EvmYul.writeBytes bytes 0 machine address length).memory.size := by
    simpa [MemoryContract.wordBytes] using hWrittenEnd
  change
    (EvmYul.writeBytes bytes 0 machine address length).memory.readWithPadding
          query 32 =
      machine.memory.readWithPadding query 32
  rw [readWithPadding_word_eq_extract _ _ hWrittenEnd32,
    readWithPadding_word_eq_extract _ _ hReadEnd32]
  apply byteArray_ext_of_size_get
  · simp [ByteArray.size_extract, hWrittenEnd32, hReadEnd32]
  · intro index hLeft hRight
    rw [ByteArray.get_extract hLeft,
      ByteArray.get_extract hRight]
    have hIndexLt : index < MemoryContract.wordBytes := by
      simpa [MemoryContract.wordBytes,
        Nat.min_eq_left hReadEnd32] using hRight
    have hOriginal :
        query + index < machine.memory.size := by
      omega
    have hWritten :
        query + index <
          (EvmYul.writeBytes bytes 0 machine address length).memory.size :=
      lt_of_lt_of_le hOriginal hSizeGe
    rw [← byteAt_eq_get _ _ hWritten,
      ← byteAt_eq_get _ _ hOriginal]
    apply
      byteAt_writeBytes_of_outside
        bytes machine address length (query + index)
        hLength hPositive hHost
    rcases hDisjoint with hBefore | hAfter
    · left
      omega
    · right
      omega

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

private theorem readWithoutPadding_size_le
    (memory : ByteArray) (address length : Nat) :
    (memory.readWithoutPadding address length).size ≤ length := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · simp [ByteArray.size_extract]
    omega

private theorem usize_wordBytes_sub_toNat
    {value : Nat} (hValue : value ≤ MemoryContract.wordBytes) :
    ((OfNat.ofNat MemoryContract.wordBytes : USize) -
        (OfNat.ofNat value : USize)).toNat =
      MemoryContract.wordBytes - value := by
  have hModulus :
      MemoryContract.wordBytes <
        2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;>
      simp [h, MemoryContract.wordBytes]
  have hWord :
      (OfNat.ofNat MemoryContract.wordBytes : USize).toNat =
        MemoryContract.wordBytes :=
    USize.toNat_ofNat_of_lt
      (by simpa [USize.size_eq_two_pow] using hModulus)
  have hValueNat :
      (OfNat.ofNat value : USize).toNat = value :=
    USize.toNat_ofNat_of_lt
      (lt_of_le_of_lt hValue hModulus)
  rw [USize.toNat_sub_of_le]
  · rw [hWord, hValueNat]
  · rw [USize.le_iff_toNat_le, hWord, hValueNat]
    exact hValue

private theorem readWithPadding_word_size
    (memory : ByteArray) (address : Nat) :
    (memory.readWithPadding address MemoryContract.wordBytes).size =
      MemoryContract.wordBytes := by
  unfold ByteArray.readWithPadding
  rw [if_neg (by
    simp [MemoryContract.wordBytes])]
  simp only [ByteArray.size_append, ffi.ByteArray.size_zeroes]
  have hRead :=
    readWithoutPadding_size_le
      memory address MemoryContract.wordBytes
  change
    (memory.readWithoutPadding
        address MemoryContract.wordBytes).size +
      ((OfNat.ofNat MemoryContract.wordBytes : USize) -
        (OfNat.ofNat
          (memory.readWithoutPadding
            address MemoryContract.wordBytes).size : USize)).toNat =
      MemoryContract.wordBytes
  rw [usize_wordBytes_sub_toNat hRead]
  omega

private theorem byteAt_readWithoutPadding_of_lt
    (memory : ByteArray) (address length index : Nat)
    (hIndex :
      index <
        (memory.readWithoutPadding address length).size) :
    byteAt (memory.readWithoutPadding address length) index =
      byteAt memory (address + index) := by
  by_cases hAddress : address ≥ memory.size
  · simp [ByteArray.readWithoutPadding, hAddress] at hIndex
  · have hMemory : address + index < memory.size := by
      simp [ByteArray.readWithoutPadding, hAddress,
        ByteArray.size_extract] at hIndex
      omega
    rw [byteAt_eq_get _ _ hIndex,
      byteAt_eq_get _ _ hMemory]
    simpa [ByteArray.readWithoutPadding, hAddress] using
      (ByteArray.get_extract
        (a := memory) (start := address)
        (stop := address + min length memory.size) hIndex)

private theorem byteAt_readWithPadding_word
    (memory : ByteArray) (address index : Nat)
    (hIndex : index < MemoryContract.wordBytes) :
    byteAt
        (memory.readWithPadding address MemoryContract.wordBytes)
        index =
      byteAt memory (address + index) := by
  let read :=
    memory.readWithoutPadding address MemoryContract.wordBytes
  let padding : USize :=
    (OfNat.ofNat MemoryContract.wordBytes : USize) -
      (OfNat.ofNat read.size : USize)
  have hRead :
      read.size ≤ MemoryContract.wordBytes := by
    exact readWithoutPadding_size_le
      memory address MemoryContract.wordBytes
  have hReadDef :
      memory.readWithPadding address MemoryContract.wordBytes =
        read ++ ffi.ByteArray.zeroes padding := by
    unfold ByteArray.readWithPadding
    rw [if_neg (by
      simp [MemoryContract.wordBytes])]
    rfl
  rw [hReadDef]
  by_cases hInside : index < read.size
  · unfold byteAt
    simp only [Array.getD_eq_getD_getElem?,
      ByteArray.data_append]
    have hInsideData : index < read.data.size := by
      simpa using hInside
    rw [Array.getElem?_append_left hInsideData]
    simpa [byteAt, Array.getD_eq_getD_getElem?, read] using
      (byteAt_readWithoutPadding_of_lt
        memory address MemoryContract.wordBytes index hInside)
  · have hPastRead : read.size ≤ index :=
      Nat.le_of_not_gt hInside
    have hPaddingNat :
        padding.toNat =
        MemoryContract.wordBytes - read.size :=
      usize_wordBytes_sub_toNat hRead
    have hPaddingIndex :
        index - read.size <
          padding.toNat := by
      rw [hPaddingNat]
      omega
    have hOutput :
        byteAt
            (read ++ ffi.ByteArray.zeroes padding)
            index =
          0 := by
      unfold byteAt
      simp only [Array.getD_eq_getD_getElem?,
        ByteArray.data_append]
      have hPastReadData : read.data.size ≤ index := by
        simpa using hPastRead
      have hPaddingIndexData :
          index - read.data.size < padding.toNat := by
        simpa using hPaddingIndex
      rw [Array.getElem?_append_right hPastReadData,
        ffi.ByteArray.data_getElem?_zeroes,
        if_pos hPaddingIndexData]
      rfl
    have hMemoryPast : memory.size ≤ address + index := by
      by_contra hNotPast
      have hMemoryIndex : address + index < memory.size :=
        Nat.lt_of_not_ge hNotPast
      have hIndexMin :
          index <
            min MemoryContract.wordBytes memory.size :=
        lt_min hIndex (by omega)
      have hAddressNotPast : ¬ address ≥ memory.size := by
        omega
      have hReadSize :
          read.size =
            min
                (address +
                  min MemoryContract.wordBytes memory.size)
                memory.size -
              address := by
        simp [read, ByteArray.readWithoutPadding,
          hAddressNotPast, ByteArray.size_extract]
      have : index < read.size := by
        rw [hReadSize]
        omega
      exact hInside this
    have hSource :
        byteAt memory (address + index) = 0 := by
      unfold byteAt
      rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none hMemoryPast]
      rfl
    exact hOutput.trans hSource.symm

theorem readWithPadding_word
    {reservation : MemoryContract.ScratchReservation}
    {source target : ByteArray}
    (hRel : OutsideReservation reservation source target)
    (address : Nat)
    (hAllowed :
      reservation.sourceAccessAllowed
        address MemoryContract.wordBytes) :
    source.readWithPadding address MemoryContract.wordBytes =
      target.readWithPadding address MemoryContract.wordBytes := by
  apply byteArray_ext_of_size_get
  · rw [readWithPadding_word_size, readWithPadding_word_size]
  · intro index hSource hTarget
    have hIndex : index < MemoryContract.wordBytes := by
      simpa [readWithPadding_word_size] using hSource
    rw [← byteAt_eq_get _ _ hSource,
      ← byteAt_eq_get _ _ hTarget,
      byteAt_readWithPadding_word source address index hIndex,
      byteAt_readWithPadding_word target address index hIndex]
    apply hRel
    intro hInside
    rcases hAllowed with hBefore | hAfter
    · exact (not_le_of_gt (by omega)) hInside.1
    · exact (not_lt_of_ge (by omega)) hInside.2

theorem write_both
    {reservation : MemoryContract.ScratchReservation}
    {source target : ByteArray}
    (copied : ByteArray)
    (sourceAddress destAddress length : Nat)
    (hRel : OutsideReservation reservation source target)
    (hHost : destAddress + length < USize.size) :
    OutsideReservation reservation
      (copied.write sourceAddress source destAddress length)
      (copied.write sourceAddress target destAddress length) := by
  intro query hOutsideReservation
  by_cases hBefore : query < destAddress
  · rw [byteAt_write_of_outside copied source sourceAddress
        destAddress length query hHost (Or.inl hBefore),
      byteAt_write_of_outside copied target sourceAddress
        destAddress length query hHost (Or.inl hBefore)]
    exact hRel query hOutsideReservation
  · by_cases hAfter : destAddress + length ≤ query
    · rw [byteAt_write_of_outside copied source sourceAddress
          destAddress length query hHost (Or.inr hAfter),
        byteAt_write_of_outside copied target sourceAddress
          destAddress length query hHost (Or.inr hAfter)]
      exact hRel query hOutsideReservation
    · rw [byteAt_write_of_inside copied source sourceAddress
          destAddress length query hHost
          (Nat.le_of_not_gt hBefore) (Nat.lt_of_not_ge hAfter),
        byteAt_write_of_inside copied target sourceAddress
          destAddress length query hHost
          (Nat.le_of_not_gt hBefore) (Nat.lt_of_not_ge hAfter)]

/--
`MCOPY` may use related source and target memories as its respective copy
buffers. When the read range is outside the compiler reservation, both copies
write the same bytes and preserve the outside-reservation relation.
-/
theorem write_self_both
    {reservation : MemoryContract.ScratchReservation}
    {source target : ByteArray}
    (sourceAddress destAddress length : Nat)
    (hRel : OutsideReservation reservation source target)
    (hSourceAllowed :
      reservation.sourceAccessAllowed sourceAddress length)
    (hHost : destAddress + length < USize.size) :
    OutsideReservation reservation
      (source.write sourceAddress source destAddress length)
      (target.write sourceAddress target destAddress length) := by
  intro query hOutsideReservation
  by_cases hBefore : query < destAddress
  · rw [byteAt_write_of_outside source source sourceAddress
        destAddress length query hHost (Or.inl hBefore),
      byteAt_write_of_outside target target sourceAddress
        destAddress length query hHost (Or.inl hBefore)]
    exact hRel query hOutsideReservation
  · by_cases hAfter : destAddress + length ≤ query
    · rw [byteAt_write_of_outside source source sourceAddress
          destAddress length query hHost (Or.inr hAfter),
        byteAt_write_of_outside target target sourceAddress
          destAddress length query hHost (Or.inr hAfter)]
      exact hRel query hOutsideReservation
    · have hStart : destAddress ≤ query :=
        Nat.le_of_not_gt hBefore
      have hEnd : query < destAddress + length :=
        Nat.lt_of_not_ge hAfter
      rw [byteAt_write_of_inside source source sourceAddress
          destAddress length query hHost hStart hEnd,
        byteAt_write_of_inside target target sourceAddress
          destAddress length query hHost hStart hEnd]
      apply hRel
      intro hInside
      rcases hSourceAllowed with hReadBefore | hReadAfter
      · exact
          (not_le_of_gt (show
              sourceAddress + (query - destAddress) <
                reservation.base by omega))
            hInside.1
      · exact
          (not_lt_of_ge (show
              reservation.endExclusive ≤
                sourceAddress + (query - destAddress) by omega))
            hInside.2

theorem writeBytes_both
    {reservation : MemoryContract.ScratchReservation}
    {source target : EvmYul.MachineState}
    (bytes : ByteArray) (address length : Nat)
    (hRel : OutsideReservation reservation source.memory target.memory)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size) :
    OutsideReservation reservation
      (EvmYul.writeBytes bytes 0 source address length).memory
      (EvmYul.writeBytes bytes 0 target address length).memory := by
  intro query hOutsideReservation
  by_cases hBefore : query < address
  · rw [byteAt_writeBytes_of_outside
        bytes source address length query hLength hPositive hHost
        (Or.inl hBefore),
      byteAt_writeBytes_of_outside
        bytes target address length query hLength hPositive hHost
        (Or.inl hBefore)]
    exact hRel query hOutsideReservation
  · by_cases hAfter : address + length ≤ query
    · rw [byteAt_writeBytes_of_outside
          bytes source address length query hLength hPositive hHost
          (Or.inr hAfter),
        byteAt_writeBytes_of_outside
          bytes target address length query hLength hPositive hHost
          (Or.inr hAfter)]
      exact hRel query hOutsideReservation
    · rw [byteAt_writeBytes_of_inside
          bytes source address length query hLength hPositive hHost
          (Nat.le_of_not_gt hBefore) (Nat.lt_of_not_ge hAfter),
        byteAt_writeBytes_of_inside
          bytes target address length query hLength hPositive hHost
          (Nat.le_of_not_gt hBefore) (Nat.lt_of_not_ge hAfter)]

theorem writeWord_both
    {reservation : MemoryContract.ScratchReservation}
    {source target : EvmYul.MachineState}
    (address : Nat) (value : EvmYul.UInt256)
    (hRel : OutsideReservation reservation source.memory target.memory)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size) :
    OutsideReservation reservation
      (source.writeWord
        (EvmYul.UInt256.ofNat address) value).memory
      (target.writeWord
        (EvmYul.UInt256.ofNat address) value).memory := by
  intro query hOutsideReservation
  by_cases hBefore : query < address
  · rw [byteAt_writeWord_of_outside value source address query
        hAddress (by simpa [MemoryContract.wordBytes] using hHost)
        (Or.inl hBefore),
      byteAt_writeWord_of_outside value target address query
        hAddress (by simpa [MemoryContract.wordBytes] using hHost)
        (Or.inl hBefore)]
    exact hRel query hOutsideReservation
  · by_cases hAfter :
        address + MemoryContract.wordBytes ≤ query
    · rw [byteAt_writeWord_of_outside value source address query
          hAddress (by simpa [MemoryContract.wordBytes] using hHost)
          (Or.inr (by simpa [MemoryContract.wordBytes] using hAfter)),
        byteAt_writeWord_of_outside value target address query
          hAddress (by simpa [MemoryContract.wordBytes] using hHost)
          (Or.inr (by simpa [MemoryContract.wordBytes] using hAfter))]
      exact hRel query hOutsideReservation
    · have hQuery :
          address + (query - address) = query := by
        omega
      have hIndex :
          query - address < MemoryContract.wordBytes := by
        omega
      have hSourceRead :=
        readWithPadding_writeWord_same_growing
          source address value hAddress
            (by simpa [MemoryContract.wordBytes] using hHost)
      have hTargetRead :=
        readWithPadding_writeWord_same_growing
          target address value hAddress
            (by simpa [MemoryContract.wordBytes] using hHost)
      calc
        byteAt
            (source.writeWord
              (EvmYul.UInt256.ofNat address) value).memory query =
          byteAt
            (source.writeWord
              (EvmYul.UInt256.ofNat address) value).memory
            (address + (query - address)) := by rw [hQuery]
        _ =
          byteAt
            ((source.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
                address MemoryContract.wordBytes)
            (query - address) := by
              exact
                (byteAt_readWithPadding_word
                  (source.writeWord
                    (EvmYul.UInt256.ofNat address) value).memory
                  address (query - address) hIndex).symm
        _ = byteAt value.toByteArray (query - address) := by
          rw [show
              (source.writeWord
                (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
                  address MemoryContract.wordBytes =
                value.toByteArray by
            simpa [MemoryContract.wordBytes] using hSourceRead]
        _ = byteAt
            ((target.writeWord
              (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
                address MemoryContract.wordBytes)
            (query - address) := by
          rw [show
              (target.writeWord
                (EvmYul.UInt256.ofNat address) value).memory.readWithPadding
                  address MemoryContract.wordBytes =
                value.toByteArray by
            simpa [MemoryContract.wordBytes] using hTargetRead]
        _ = byteAt
            (target.writeWord
              (EvmYul.UInt256.ofNat address) value).memory
            (address + (query - address)) := by
              exact
                byteAt_readWithPadding_word
                  (target.writeWord
                    (EvmYul.UInt256.ofNat address) value).memory
                  address (query - address) hIndex
        _ =
          byteAt
            (target.writeWord
              (EvmYul.UInt256.ofNat address) value).memory query := by
              rw [hQuery]

private theorem byteArray_zeroes_eq_replicate (size : USize) :
    ffi.ByteArray.zeroes size =
      ⟨Array.replicate size.toNat 0⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp [ffi.ByteArray.size_zeroes]
  · intro index hLeft hRight
    have hGet :=
      ffi.ByteArray.data_getElem?_zeroes size index
    rw [if_pos (by simpa using hLeft)] at hGet
    rw [Array.getElem?_eq_getElem hLeft] at hGet
    have hLeftValue :
        (ffi.ByteArray.zeroes size).data[index] = 0 :=
      Option.some.inj hGet
    simpa using hLeftValue

private theorem fromBytes'_replicate_zero (size : Nat) :
    EvmYul.fromBytes' (List.replicate size 0) = 0 := by
  induction size with
  | zero =>
      rfl
  | succ size ih =>
      simp [List.replicate, EvmYul.fromBytes', ih]

private theorem fromByteArrayBigEndian_zeroes (size : USize) :
    EvmYul.fromByteArrayBigEndian
        (ffi.ByteArray.zeroes size) =
      0 := by
  rw [byteArray_zeroes_eq_replicate]
  simp [EvmYul.fromByteArrayBigEndian,
    EvmYul.fromBytesBigEndian, EvmYul.fromBytes',
    Function.comp_apply,
    fromBytes'_replicate_zero]

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

theorem lookupMemory_mstore_disjoint_growing
    (machine : EvmYul.MachineState) (address query : Nat)
    (value : EvmYul.UInt256)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query)
    (hHost : address + 32 < USize.size)
    (hReadMemory : query + 32 ≤ machine.memory.size)
    (hReadActive :
      query + 32 ≤ machine.activeWords.toNat * 32)
    (hActiveNoWrap :
      machine.activeWords.toNat * 32 < EvmYul.UInt256.size)
    (hDisjoint :
      query + 32 ≤ address ∨ address + 32 ≤ query) :
    (machine.mstore
        (EvmYul.UInt256.ofNat address) value).lookupMemory
          (EvmYul.UInt256.ofNat query) =
      machine.lookupMemory (EvmYul.UInt256.ofNat query) := by
  let written :=
    machine.mstore (EvmYul.UInt256.ofNat address) value
  have hSizeGe :=
    writeWord_memory_size_ge
      machine address value hAddress hHost
  have hWrittenReadMemory :
      query + 32 ≤ written.memory.size := by
    simpa [written, EvmYul.MachineState.mstore] using
      hReadMemory.trans hSizeGe
  have hEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size := by
    simpa [MemoryContract.wordBytes] using
      (lt_trans hHost usize_size_lt_uint256_size)
  have hActiveMono :=
    activeWords_toNat_le_mstore machine address value hEnd
  have hWrittenReadActive :
      query + 32 ≤ written.activeWords.toNat * 32 := by
    exact hReadActive.trans
      (Nat.mul_le_mul_right 32 (by simpa [written] using hActiveMono))
  have hWrittenActiveNoWrap :
      written.activeWords.toNat * 32 < EvmYul.UInt256.size := by
    simpa [written] using
      (mstore_activeBytes_lt_size_of_activeBytes_lt_size
        machine address value hActiveNoWrap hHost)
  have hQueryLt : query < EvmYul.UInt256.size := by
    have hSize := usize_size_lt_uint256_size
    omega
  have hProduct
      (words : EvmYul.UInt256)
      (hNoWrap : words.toNat * 32 < EvmYul.UInt256.size) :
      (words * (⟨32⟩ : EvmYul.UInt256)).toNat =
        words.toNat * 32 := by
    have hMod :
        (words * (⟨32⟩ : EvmYul.UInt256)).toNat =
          (words.toNat * 32) % EvmYul.UInt256.size := by
      change
        (EvmYul.UInt256.mul words
          (⟨32⟩ : EvmYul.UInt256)).toNat =
            (words.toNat * 32) % EvmYul.UInt256.size
      unfold EvmYul.UInt256.mul EvmYul.UInt256.toNat
      rfl
    rw [hMod, Nat.mod_eq_of_lt hNoWrap]
  have hSourceGuard :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ machine.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          machine.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    simp only [not_or, not_le]
    constructor
    · simpa [hQuery] using
        (show query < machine.memory.size by omega)
    · intro hLe
      have hLeNat :
          (machine.activeWords *
              (⟨32⟩ : EvmYul.UInt256)).toNat ≤
            (EvmYul.UInt256.ofNat query).toNat :=
        hLe
      rw [hProduct machine.activeWords hActiveNoWrap,
        EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt] at hLeNat
      omega
  have hWrittenGuard :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ written.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          written.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    simp only [not_or, not_le]
    constructor
    · simpa [hQuery] using
        (show query < written.memory.size by omega)
    · intro hLe
      have hLeNat :
          (written.activeWords *
              (⟨32⟩ : EvmYul.UInt256)).toNat ≤
            (EvmYul.UInt256.ofNat query).toNat :=
        hLe
      rw [hProduct written.activeWords hWrittenActiveNoWrap,
        EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt] at hLeNat
      omega
  unfold EvmYul.MachineState.lookupMemory
  rw [if_neg hWrittenGuard, if_neg hSourceGuard]
  simp only [written, EvmYul.MachineState.mstore, hQuery]
  rw [readWithPadding_writeWord_disjoint_growing
    machine address query value hAddress hHost hReadMemory hDisjoint]

/--
Machine-state relation used across allocation lowering.

Remaining gas is intentionally unobservable here: exact `gas()` values live in
the ordered replay transcript. Stack allocation keeps memory and active size
equal. Scratch allocation permits differences only inside the source-reserved
interval and permits target memory expansion beyond the source extent.
-/
def MemoryConsistent (machine : EvmYul.MachineState) : Prop :=
  machine.memory.size ≤
    machine.activeWords.toNat * MemoryContract.wordBytes

/--
The active-memory extent induced by a source memory region is representable
without wrapping the `UInt256` value observed by `MSIZE`.
-/
def ExpansionNoWrap (address size : Nat) : Prop :=
  EvmYul.MachineState.M 0 address size *
      MemoryContract.wordBytes <
    EvmYul.UInt256.size

theorem M_mono_active {left right address size : Nat}
    (hActive : left ≤ right) :
    EvmYul.MachineState.M left address size ≤
      EvmYul.MachineState.M right address size := by
  cases size with
  | zero =>
      simpa [EvmYul.MachineState.M] using hActive
  | succ size =>
      simp only [EvmYul.MachineState.M]
      exact max_le_max hActive (le_refl _)

theorem M_activeBytes_lt_of_expansionNoWrap
    {active address size : Nat}
    (hActive :
      active * MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hExpansion : ExpansionNoWrap address size) :
    EvmYul.MachineState.M active address size *
        MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  cases size with
  | zero =>
      simpa [EvmYul.MachineState.M] using hActive
  | succ size =>
      let required := (address + (size + 1) + 31) / 32
      have hRequired :
          required * MemoryContract.wordBytes < EvmYul.UInt256.size := by
        simpa [ExpansionNoWrap, EvmYul.MachineState.M, required] using
          hExpansion
      by_cases hLe : active ≤ required
      · simpa [EvmYul.MachineState.M, required, Nat.max_eq_right hLe] using
          hRequired
      · have hRequiredLe : required ≤ active :=
          Nat.le_of_not_ge hLe
        simpa [EvmYul.MachineState.M, required,
          Nat.max_eq_left hRequiredLe] using hActive

theorem activeBytes_toNat
    (machine : EvmYul.MachineState)
    (hNoWrap :
      machine.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    (machine.activeWords *
        EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat =
      machine.activeWords.toNat * MemoryContract.wordBytes := by
  have hProduct :
      (machine.activeWords *
          EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat =
        (machine.activeWords.toNat * MemoryContract.wordBytes) %
          EvmYul.UInt256.size := by
    change
      (EvmYul.UInt256.mul machine.activeWords
        (EvmYul.UInt256.ofNat MemoryContract.wordBytes)).toNat =
          (machine.activeWords.toNat * MemoryContract.wordBytes) %
            EvmYul.UInt256.size
    unfold EvmYul.UInt256.mul EvmYul.UInt256.toNat
    rfl
  rw [hProduct, Nat.mod_eq_of_lt hNoWrap]

theorem lookupMemory_eq_of_write_disjoint_growing
    (copied : ByteArray)
    (before after : EvmYul.MachineState)
    (sourceAddress address length query : Nat)
    (hHost : address + length < USize.size)
    (hMemory :
      after.memory =
        copied.write sourceAddress before.memory address length)
    (hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤ before.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        before.activeWords.toNat * MemoryContract.wordBytes)
    (hBeforeNoWrap :
      before.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hActiveMono :
      before.activeWords.toNat ≤ after.activeWords.toNat)
    (hAfterNoWrap :
      after.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hDisjoint :
      query + MemoryContract.wordBytes ≤ address ∨
        address + length ≤ query) :
    after.lookupMemory (EvmYul.UInt256.ofNat query) =
      before.lookupMemory (EvmYul.UInt256.ofNat query) := by
  have hWordPositive : 0 < MemoryContract.wordBytes := by
    decide
  have hSizeGe :=
    size_write_ge copied before.memory sourceAddress address length hHost
  have hAfterReadMemory :
      query + MemoryContract.wordBytes ≤ after.memory.size := by
    rw [hMemory]
    exact hReadMemory.trans hSizeGe
  have hAfterReadActive :
      query + MemoryContract.wordBytes ≤
        after.activeWords.toNat * MemoryContract.wordBytes := by
    exact hReadActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hActiveMono)
  have hQueryLt : query < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hBeforeNoWrap)
  have hBeforeProduct :
      (before.activeWords *
          EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat =
        before.activeWords.toNat * MemoryContract.wordBytes :=
    activeBytes_toNat before hBeforeNoWrap
  have hAfterProduct :
      (after.activeWords *
          EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat =
        after.activeWords.toNat * MemoryContract.wordBytes :=
    activeBytes_toNat after hAfterNoWrap
  have hBeforeGuard :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ before.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          before.activeWords *
            EvmYul.UInt256.ofNat MemoryContract.wordBytes) := by
    simp only [not_or, not_le]
    constructor
    · rw [hQuery]
      omega
    · intro hLe
      have hLeNat :
          (before.activeWords *
              EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat ≤
            (EvmYul.UInt256.ofNat query).toNat :=
        hLe
      rw [hBeforeProduct, hQuery] at hLeNat
      omega
  have hAfterGuard :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ after.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          after.activeWords *
            EvmYul.UInt256.ofNat MemoryContract.wordBytes) := by
    simp only [not_or, not_le]
    constructor
    · rw [hQuery]
      omega
    · intro hLe
      have hLeNat :
          (after.activeWords *
              EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat ≤
            (EvmYul.UInt256.ofNat query).toNat :=
        hLe
      rw [hAfterProduct, hQuery] at hLeNat
      omega
  have hBeforeGuard32 :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ before.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          before.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    simpa [MemoryContract.wordBytes] using hBeforeGuard
  have hAfterGuard32 :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ after.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          after.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    simpa [MemoryContract.wordBytes] using hAfterGuard
  unfold EvmYul.MachineState.lookupMemory
  rw [if_neg hAfterGuard32, if_neg hBeforeGuard32, hQuery, hMemory]
  rw [show
      (copied.write sourceAddress before.memory address length).readWithPadding
          query 32 =
        before.memory.readWithPadding query 32 by
    simpa [MemoryContract.wordBytes] using
      (readWithPadding_write_disjoint_growing
        copied before sourceAddress address length query hHost
        hReadMemory hDisjoint)]

theorem lookupMemory_eq_of_writeBytes_disjoint_growing
    (bytes : ByteArray)
    (before after : EvmYul.MachineState)
    (address length query : Nat)
    (hLength : bytes.size = length)
    (hPositive : 0 < length)
    (hHost : address + length < USize.size)
    (hMemory :
      after.memory =
        (EvmYul.writeBytes bytes 0 before address length).memory)
    (hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤ before.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        before.activeWords.toNat * MemoryContract.wordBytes)
    (hBeforeNoWrap :
      before.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hActiveMono :
      before.activeWords.toNat ≤ after.activeWords.toNat)
    (hAfterNoWrap :
      after.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hDisjoint :
      query + MemoryContract.wordBytes ≤ address ∨
        address + length ≤ query) :
    after.lookupMemory (EvmYul.UInt256.ofNat query) =
      before.lookupMemory (EvmYul.UInt256.ofNat query) := by
  exact
    lookupMemory_eq_of_write_disjoint_growing bytes before after
      0 address length query hHost
      (by simpa [EvmYul.writeBytes] using hMemory)
      hQuery hReadMemory hReadActive hBeforeNoWrap hActiveMono
      hAfterNoWrap hDisjoint

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

theorem lookupMemory_eq_of_allowed
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : MachineRel contract source target)
    (hConsistent : MemoryConsistent source)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address : EvmYul.UInt256)
    (hAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed
            address.toNat MemoryContract.wordBytes) :
    source.lookupMemory address = target.lookupMemory address := by
  cases hReservation : contract.scratch? with
  | none =>
      have hMemory : source.memory = target.memory := by
        simpa [hReservation] using hRel.memory
      have hActive : source.activeWords = target.activeWords := by
        simpa [hReservation] using hRel.activeWords
      simp [EvmYul.MachineState.lookupMemory, hMemory, hActive]
  | some reservation =>
      have hMemory :
          OutsideReservation reservation source.memory target.memory := by
        simpa [hReservation] using hRel.memory
      have hActive :
          source.activeWords.toNat ≤ target.activeWords.toNat := by
        simpa [hReservation] using hRel.activeWords
      have hAllowed' :
          reservation.sourceAccessAllowed
            address.toNat MemoryContract.wordBytes := by
        simpa [hReservation] using hAllowed
      have hRead :
          source.memory.readWithPadding
              address.toNat MemoryContract.wordBytes =
            target.memory.readWithPadding
              address.toNat MemoryContract.wordBytes :=
        hMemory.readWithPadding_word address.toNat hAllowed'
      have hRead32 :
          source.memory.readWithPadding address.toNat 32 =
            target.memory.readWithPadding address.toNat 32 := by
        simpa [MemoryContract.wordBytes] using hRead
      have hSourceNoWrap :
          source.activeWords.toNat * MemoryContract.wordBytes <
            EvmYul.UInt256.size := by
        exact lt_of_le_of_lt
          (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
          hTargetNoWrap
      have hSourceProduct :
          (source.activeWords *
              (⟨32⟩ : EvmYul.UInt256)).toNat =
            source.activeWords.toNat * MemoryContract.wordBytes := by
        simpa [MemoryContract.wordBytes] using
          activeBytes_toNat source hSourceNoWrap
      have hTargetProduct :
          (target.activeWords *
              (⟨32⟩ : EvmYul.UInt256)).toNat =
            target.activeWords.toNat * MemoryContract.wordBytes := by
        simpa [MemoryContract.wordBytes] using
          activeBytes_toNat target hTargetNoWrap
      unfold EvmYul.MachineState.lookupMemory
      by_cases hSourceGuard :
            address.toNat ≥ source.memory.size ∨
              address ≥
                source.activeWords * (⟨32⟩ : EvmYul.UInt256)
      · rw [if_pos hSourceGuard]
        by_cases hTargetGuard :
            address.toNat ≥ target.memory.size ∨
              address ≥
                target.activeWords * (⟨32⟩ : EvmYul.UInt256)
        · rw [if_pos hTargetGuard]
        · rw [if_neg hTargetGuard]
          have hSourcePast :
              source.memory.size ≤ address.toNat := by
            rcases hSourceGuard with hPast | hPast
            · exact hPast
            · have hPastNat :
                  (source.activeWords *
                      (⟨32⟩ : EvmYul.UInt256)).toNat ≤
                    address.toNat :=
                hPast
              rw [hSourceProduct] at hPastNat
              exact hConsistent.trans hPastNat
          rw [← hRead32]
          simp [ByteArray.readWithPadding,
            ByteArray.readWithoutPadding, hSourcePast,
            MemoryContract.wordBytes,
            OutsideReservation.fromByteArrayBigEndian_zeroes,
            EvmYul.UInt256.ofNat]
          rfl
      · rw [if_neg hSourceGuard]
        by_cases hTargetGuard :
            address.toNat ≥ target.memory.size ∨
              address ≥
                target.activeWords * (⟨32⟩ : EvmYul.UInt256)
        · rw [if_pos hTargetGuard]
          have hTargetPast :
              target.memory.size ≤ address.toNat := by
            rcases hTargetGuard with hPast | hPast
            · exact hPast
            · exfalso
              apply hSourceGuard
              right
              have hPastNat :
                  (target.activeWords *
                      (⟨32⟩ : EvmYul.UInt256)).toNat ≤
                    address.toNat :=
                hPast
              rw [hTargetProduct] at hPastNat
              have hSourcePastNat :
                  (source.activeWords *
                      (⟨32⟩ : EvmYul.UInt256)).toNat ≤
                    address.toNat := by
                rw [hSourceProduct]
                exact
                  (Nat.mul_le_mul_right
                    MemoryContract.wordBytes hActive).trans hPastNat
              exact hSourcePastNat
          rw [hRead32]
          simp [ByteArray.readWithPadding,
            ByteArray.readWithoutPadding, hTargetPast,
            MemoryContract.wordBytes,
            OutsideReservation.fromByteArrayBigEndian_zeroes,
            EvmYul.UInt256.ofNat]
          rfl
        · rw [if_neg hTargetGuard, hRead32]

theorem lookupMemory_eq_of_memory_eq_active_growth
    {before after : EvmYul.MachineState}
    (query : Nat)
    (hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query)
    (hMemory : after.memory = before.memory)
    (hActive :
      before.activeWords.toNat ≤ after.activeWords.toNat)
    (hBeforeNoWrap :
      before.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hAfterNoWrap :
      after.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤ before.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        before.activeWords.toNat * MemoryContract.wordBytes) :
    after.lookupMemory (EvmYul.UInt256.ofNat query) =
      before.lookupMemory (EvmYul.UInt256.ofNat query) := by
  have hPositive : 0 < MemoryContract.wordBytes := by decide
  have hQueryLt : query < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hBeforeNoWrap)
  have hAfterReadMemory :
      query + MemoryContract.wordBytes ≤ after.memory.size := by
    simpa [hMemory] using hReadMemory
  have hAfterReadActive :
      query + MemoryContract.wordBytes ≤
        after.activeWords.toNat * MemoryContract.wordBytes := by
    exact hReadActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
  have hBeforeProduct :
      (before.activeWords *
          EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat =
        before.activeWords.toNat * MemoryContract.wordBytes :=
    activeBytes_toNat before hBeforeNoWrap
  have hAfterProduct :
      (after.activeWords *
          EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat =
        after.activeWords.toNat * MemoryContract.wordBytes :=
    activeBytes_toNat after hAfterNoWrap
  have hBeforeGuard :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ before.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          before.activeWords * EvmYul.UInt256.ofNat
            MemoryContract.wordBytes) := by
    simp only [not_or, not_le]
    constructor
    · rw [hQuery]
      omega
    · intro hLe
      have hLeNat :
          (before.activeWords *
              EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat ≤
            (EvmYul.UInt256.ofNat query).toNat :=
        hLe
      rw [hBeforeProduct, hQuery] at hLeNat
      omega
  have hAfterGuard :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ after.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          after.activeWords * EvmYul.UInt256.ofNat
            MemoryContract.wordBytes) := by
    simp only [not_or, not_le]
    constructor
    · rw [hQuery]
      omega
    · intro hLe
      have hLeNat :
          (after.activeWords *
              EvmYul.UInt256.ofNat MemoryContract.wordBytes).toNat ≤
            (EvmYul.UInt256.ofNat query).toNat :=
        hLe
      rw [hAfterProduct, hQuery] at hLeNat
      omega
  have hBeforeGuard32 :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ before.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          before.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    simpa [MemoryContract.wordBytes] using hBeforeGuard
  have hAfterGuard32 :
      ¬ ((EvmYul.UInt256.ofNat query).toNat ≥ after.memory.size ∨
        EvmYul.UInt256.ofNat query ≥
          after.activeWords * (⟨32⟩ : EvmYul.UInt256)) := by
    simpa [MemoryContract.wordBytes] using hAfterGuard
  unfold EvmYul.MachineState.lookupMemory
  rw [if_neg hAfterGuard32, if_neg hBeforeGuard32, hQuery, hMemory]

theorem mload_of_allowed
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : MachineRel contract source target)
    (hConsistent : MemoryConsistent source)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address : EvmYul.UInt256)
    (hAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed
            address.toNat MemoryContract.wordBytes)
    (hExpansion :
      ExpansionNoWrap address.toNat MemoryContract.wordBytes) :
    (source.mload address).1 = (target.mload address).1 ∧
      MachineRel contract
        (source.mload address).2 (target.mload address).2 ∧
      (target.mload address).2.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size ∧
      target.activeWords.toNat ≤
        (target.mload address).2.activeWords.toNat := by
  have hLookup :=
    lookupMemory_eq_of_allowed hRel hConsistent hTargetNoWrap
      address hAllowed
  have hTargetExpanded :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat MemoryContract.wordBytes *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    M_activeBytes_lt_of_expansionNoWrap hTargetNoWrap hExpansion
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  have hTargetActive :
      (target.mload address).2.activeWords.toNat =
        EvmYul.MachineState.M target.activeWords.toNat
          address.toNat MemoryContract.wordBytes := by
    change
      (EvmYul.UInt256.ofNat
          (EvmYul.MachineState.M target.activeWords.toNat
            address.toNat 32)).toNat =
        EvmYul.MachineState.M target.activeWords.toNat address.toNat 32
    exact EvmYul.UInt256.toNat_ofNat_of_lt
      (by simpa [MemoryContract.wordBytes] using hTargetM)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [EvmYul.MachineState.mload] using hLookup
  · cases hReservation : contract.scratch? with
    | none =>
        have hMemory : source.memory = target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive : source.activeWords = target.activeWords := by
          simpa [hReservation] using hRel.activeWords
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · simpa [hReservation, EvmYul.MachineState.mload] using hMemory
        · simpa [hReservation, EvmYul.MachineState.mload, hActive]
        · simpa [EvmYul.MachineState.mload] using hRel.returnData
        · simpa [EvmYul.MachineState.mload] using hRel.output
    | some reservation =>
        have hActive :
            source.activeWords.toNat ≤ target.activeWords.toNat := by
          simpa [hReservation] using hRel.activeWords
        have hSourceNoWrap :
            source.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          exact lt_of_le_of_lt
            (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
            hTargetNoWrap
        have hSourceExpanded :
            EvmYul.MachineState.M source.activeWords.toNat
                address.toNat MemoryContract.wordBytes *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size :=
          M_activeBytes_lt_of_expansionNoWrap hSourceNoWrap hExpansion
        have hSourceM :
            EvmYul.MachineState.M source.activeWords.toNat
                address.toNat MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          have hPositive : 0 < MemoryContract.wordBytes := by decide
          nlinarith
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · simpa [hReservation, EvmYul.MachineState.mload] using hRel.memory
        · simp only [hReservation]
          change
            (EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M source.activeWords.toNat
                  address.toNat MemoryContract.wordBytes)).toNat ≤
              (EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M target.activeWords.toNat
                  address.toNat MemoryContract.wordBytes)).toNat
          rw [EvmYul.UInt256.toNat_ofNat_of_lt hSourceM,
            EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
          exact M_mono_active hActive
        · simpa [EvmYul.MachineState.mload] using hRel.returnData
        · simpa [EvmYul.MachineState.mload] using hRel.output
  · rw [hTargetActive]
    exact hTargetExpanded
  · rw [hTargetActive]
    simp [EvmYul.MachineState.M, MemoryContract.wordBytes]

theorem mstore_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address value : EvmYul.UInt256)
    (hExpansion :
      ExpansionNoWrap address.toNat MemoryContract.wordBytes)
    (hHost :
      address.toNat + MemoryContract.wordBytes < USize.size) :
    MachineRel contract
        (source.mstore address value) (target.mstore address value) ∧
      (target.mstore address value).activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size ∧
      target.activeWords.toNat ≤
        (target.mstore address value).activeWords.toNat ∧
      target.memory.size ≤
        (target.mstore address value).memory.size := by
  have hAddressWord :
      EvmYul.UInt256.ofNat address.toNat = address :=
    EvmYul.UInt256.ofNat_toNat address
  have hAddress :
      (EvmYul.UInt256.ofNat address.toNat).toNat = address.toNat := by
    rw [hAddressWord]
  have hTargetExpanded :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat MemoryContract.wordBytes *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    M_activeBytes_lt_of_expansionNoWrap hTargetNoWrap hExpansion
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  have hTargetActive :
      (target.mstore address value).activeWords.toNat =
        EvmYul.MachineState.M target.activeWords.toNat
          address.toNat MemoryContract.wordBytes := by
    change
      (EvmYul.UInt256.ofNat
          (EvmYul.MachineState.M target.activeWords.toNat
            address.toNat 32)).toNat =
        EvmYul.MachineState.M target.activeWords.toNat address.toNat 32
    exact EvmYul.UInt256.toNat_ofNat_of_lt
      (by simpa [MemoryContract.wordBytes] using hTargetM)
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hReservation : contract.scratch? with
    | none =>
        have hMemory : source.memory = target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive : source.activeWords = target.activeWords := by
          simpa [hReservation] using hRel.activeWords
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          change
            (source.writeWord address value).memory =
              (target.writeWord address value).memory
          unfold EvmYul.MachineState.writeWord EvmYul.writeBytes
          simp [hMemory]
        · rw [hReservation]
          change
            EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M source.activeWords.toNat
                  address.toNat 32) =
              EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M target.activeWords.toNat
                  address.toNat 32)
          rw [hActive]
        · simpa [EvmYul.MachineState.mstore] using hRel.returnData
        · simpa [EvmYul.MachineState.mstore] using hRel.output
    | some reservation =>
        have hMemory :
            OutsideReservation reservation source.memory target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive :
            source.activeWords.toNat ≤ target.activeWords.toNat := by
          simpa [hReservation] using hRel.activeWords
        have hSourceNoWrap :
            source.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          exact lt_of_le_of_lt
            (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
            hTargetNoWrap
        have hSourceExpanded :
            EvmYul.MachineState.M source.activeWords.toNat
                address.toNat MemoryContract.wordBytes *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size :=
          M_activeBytes_lt_of_expansionNoWrap hSourceNoWrap hExpansion
        have hSourceM :
            EvmYul.MachineState.M source.activeWords.toNat
                address.toNat MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          have hPositive : 0 < MemoryContract.wordBytes := by decide
          nlinarith
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          simpa [EvmYul.MachineState.mstore, hAddressWord] using
            (OutsideReservation.writeWord_both
              address.toNat value hMemory hAddress hHost)
        · simp only [hReservation]
          change
            (EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M source.activeWords.toNat
                  address.toNat MemoryContract.wordBytes)).toNat ≤
              (EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M target.activeWords.toNat
                  address.toNat MemoryContract.wordBytes)).toNat
          rw [EvmYul.UInt256.toNat_ofNat_of_lt hSourceM,
            EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
          exact M_mono_active hActive
        · simpa [EvmYul.MachineState.mstore] using hRel.returnData
        · simpa [EvmYul.MachineState.mstore] using hRel.output
  · rw [hTargetActive]
    exact hTargetExpanded
  · rw [hTargetActive]
    simp [EvmYul.MachineState.M, MemoryContract.wordBytes]
  · simpa [EvmYul.MachineState.mstore, hAddressWord] using
      (writeWord_memory_size_ge target address.toNat value hAddress
        (by simpa [MemoryContract.wordBytes] using hHost))

set_option maxHeartbeats 1000000 in
theorem mstore8_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address value : EvmYul.UInt256)
    (hExpansion : ExpansionNoWrap address.toNat 1)
    (hHost : address.toNat + 1 < USize.size) :
    MachineRel contract
        (source.mstore8 address value) (target.mstore8 address value) ∧
      (target.mstore8 address value).activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size ∧
      target.activeWords.toNat ≤
        (target.mstore8 address value).activeWords.toNat ∧
      target.memory.size ≤
        (target.mstore8 address value).memory.size := by
  let bytes : ByteArray := ⟨#[UInt8.ofNat value.toNat]⟩
  have hBytes : bytes.size = 1 := by
    rfl
  have hTargetExpanded :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat 1 * MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    M_activeBytes_lt_of_expansionNoWrap hTargetNoWrap hExpansion
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat address.toNat 1 <
        EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  have hTargetActive :
      (target.mstore8 address value).activeWords.toNat =
        EvmYul.MachineState.M target.activeWords.toNat
          address.toNat 1 := by
    change
      (EvmYul.UInt256.ofNat
          (EvmYul.MachineState.M target.activeWords.toNat
            address.toNat 1)).toNat =
        EvmYul.MachineState.M target.activeWords.toNat address.toNat 1
    exact EvmYul.UInt256.toNat_ofNat_of_lt hTargetM
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hReservation : contract.scratch? with
    | none =>
        have hMemory : source.memory = target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive : source.activeWords = target.activeWords := by
          simpa [hReservation] using hRel.activeWords
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          change
            (EvmYul.writeBytes bytes 0 source address.toNat 1).memory =
              (EvmYul.writeBytes bytes 0 target address.toNat 1).memory
          unfold EvmYul.writeBytes
          simp [hMemory]
        · rw [hReservation]
          change
            EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M source.activeWords.toNat
                  address.toNat 1) =
              EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M target.activeWords.toNat
                  address.toNat 1)
          rw [hActive]
        · simpa [EvmYul.MachineState.mstore8] using hRel.returnData
        · simpa [EvmYul.MachineState.mstore8] using hRel.output
    | some reservation =>
        have hMemory :
            OutsideReservation reservation source.memory target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive :
            source.activeWords.toNat ≤ target.activeWords.toNat := by
          simpa [hReservation] using hRel.activeWords
        have hSourceNoWrap :
            source.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          exact lt_of_le_of_lt
            (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
            hTargetNoWrap
        have hSourceExpanded :
            EvmYul.MachineState.M source.activeWords.toNat
                address.toNat 1 * MemoryContract.wordBytes <
              EvmYul.UInt256.size :=
          M_activeBytes_lt_of_expansionNoWrap hSourceNoWrap hExpansion
        have hSourceM :
            EvmYul.MachineState.M source.activeWords.toNat address.toNat 1 <
              EvmYul.UInt256.size := by
          have hPositive : 0 < MemoryContract.wordBytes := by decide
          nlinarith
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          simpa [EvmYul.MachineState.mstore8, bytes] using
            (OutsideReservation.writeBytes_both
              bytes address.toNat 1 hMemory hBytes (by decide) hHost)
        · simp only [hReservation]
          change
            (EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M source.activeWords.toNat
                  address.toNat 1)).toNat ≤
              (EvmYul.UInt256.ofNat
                (EvmYul.MachineState.M target.activeWords.toNat
                  address.toNat 1)).toNat
          rw [EvmYul.UInt256.toNat_ofNat_of_lt hSourceM,
            EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
          exact M_mono_active hActive
        · simpa [EvmYul.MachineState.mstore8] using hRel.returnData
        · simpa [EvmYul.MachineState.mstore8] using hRel.output
  · rw [hTargetActive]
    exact hTargetExpanded
  · rw [hTargetActive]
    simp [EvmYul.MachineState.M]
  · simpa [EvmYul.MachineState.mstore8, bytes] using
      (writeBytes_memory_size_ge bytes target address.toNat 1
        hBytes (by decide) hHost)

theorem copy_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (copied : ByteArray)
    (sourceAddress address length : Nat)
    (hExpansion : ExpansionNoWrap address length)
    (hHost : address + length < USize.size) :
    let sourceFinal : EvmYul.MachineState :=
      { source with
        memory := copied.write sourceAddress source.memory address length
        activeWords :=
          EvmYul.UInt256.ofNat
            (EvmYul.MachineState.M
              source.activeWords.toNat address length) }
    let targetFinal : EvmYul.MachineState :=
      { target with
        memory := copied.write sourceAddress target.memory address length
        activeWords :=
          EvmYul.UInt256.ofNat
            (EvmYul.MachineState.M
              target.activeWords.toNat address length) }
    MachineRel contract sourceFinal targetFinal ∧
      targetFinal.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size ∧
      target.activeWords.toNat ≤ targetFinal.activeWords.toNat ∧
      target.memory.size ≤ targetFinal.memory.size := by
  dsimp
  have hTargetExpanded :
      EvmYul.MachineState.M target.activeWords.toNat address length *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    M_activeBytes_lt_of_expansionNoWrap hTargetNoWrap hExpansion
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat address length <
        EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hReservation : contract.scratch? with
    | none =>
        have hMemory : source.memory = target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive : source.activeWords = target.activeWords := by
          simpa [hReservation] using hRel.activeWords
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          simp [hMemory]
        · rw [hReservation, hActive]
        · exact hRel.returnData
        · exact hRel.output
    | some reservation =>
        have hMemory :
            OutsideReservation reservation source.memory target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive :
            source.activeWords.toNat ≤ target.activeWords.toNat := by
          simpa [hReservation] using hRel.activeWords
        have hSourceNoWrap :
            source.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          exact lt_of_le_of_lt
            (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
            hTargetNoWrap
        have hSourceExpanded :
            EvmYul.MachineState.M source.activeWords.toNat address length *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size :=
          M_activeBytes_lt_of_expansionNoWrap hSourceNoWrap hExpansion
        have hSourceM :
            EvmYul.MachineState.M source.activeWords.toNat address length <
              EvmYul.UInt256.size := by
          have hPositive : 0 < MemoryContract.wordBytes := by decide
          nlinarith
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          exact
            OutsideReservation.write_both copied sourceAddress
              address length hMemory hHost
        · simp only [hReservation]
          rw [EvmYul.UInt256.toNat_ofNat_of_lt hSourceM,
            EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
          exact M_mono_active hActive
        · exact hRel.returnData
        · exact hRel.output
  · rw [EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
    exact hTargetExpanded
  · rw [EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
    exact
      (show target.activeWords.toNat ≤
          EvmYul.MachineState.M target.activeWords.toNat address length by
        cases length <;> simp [EvmYul.MachineState.M])
  · exact
      size_write_ge copied target.memory sourceAddress
        address length hHost

/--
Related machines agree after `MCOPY` when its read range is outside the
compiler reservation. The destination may grow each memory independently; the
relation records the target's monotone active-memory and materialized-size
growth.
-/
theorem mcopy_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (sourceAddress address length : Nat)
    (hSourceAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed sourceAddress length)
    (hExpansion : ExpansionNoWrap (max address sourceAddress) length)
    (hHost : address + length < USize.size) :
    let sourceFinal : EvmYul.MachineState :=
      { source with
        memory :=
          source.memory.write sourceAddress source.memory address length
        activeWords :=
          EvmYul.UInt256.ofNat
            (EvmYul.MachineState.M source.activeWords.toNat
              (max address sourceAddress) length) }
    let targetFinal : EvmYul.MachineState :=
      { target with
        memory :=
          target.memory.write sourceAddress target.memory address length
        activeWords :=
          EvmYul.UInt256.ofNat
            (EvmYul.MachineState.M target.activeWords.toNat
              (max address sourceAddress) length) }
    MachineRel contract sourceFinal targetFinal ∧
      targetFinal.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size ∧
      target.activeWords.toNat ≤ targetFinal.activeWords.toNat ∧
      target.memory.size ≤ targetFinal.memory.size := by
  dsimp
  let expansionAddress := max address sourceAddress
  have hTargetExpanded :
      EvmYul.MachineState.M target.activeWords.toNat
            expansionAddress length *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    M_activeBytes_lt_of_expansionNoWrap hTargetNoWrap hExpansion
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat
          expansionAddress length <
        EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hReservation : contract.scratch? with
    | none =>
        have hMemory : source.memory = target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive : source.activeWords = target.activeWords := by
          simpa [hReservation] using hRel.activeWords
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          simp [hMemory]
        · rw [hReservation, hActive]
        · exact hRel.returnData
        · exact hRel.output
    | some reservation =>
        have hMemory :
            OutsideReservation reservation source.memory target.memory := by
          simpa [hReservation] using hRel.memory
        have hActive :
            source.activeWords.toNat ≤ target.activeWords.toNat := by
          simpa [hReservation] using hRel.activeWords
        have hSourceNoWrap :
            source.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          exact lt_of_le_of_lt
            (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
            hTargetNoWrap
        have hSourceExpanded :
            EvmYul.MachineState.M source.activeWords.toNat
                  expansionAddress length *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size :=
          M_activeBytes_lt_of_expansionNoWrap hSourceNoWrap hExpansion
        have hSourceM :
            EvmYul.MachineState.M source.activeWords.toNat
                expansionAddress length <
              EvmYul.UInt256.size := by
          have hPositive : 0 < MemoryContract.wordBytes := by decide
          nlinarith
        have hReadAllowed :
            reservation.sourceAccessAllowed sourceAddress length := by
          simpa [hReservation] using hSourceAllowed
        refine
          { memory := ?_
            activeWords := ?_
            returnData := ?_
            output := ?_ }
        · rw [hReservation]
          exact
            OutsideReservation.write_self_both
              sourceAddress address length hMemory hReadAllowed hHost
        · simp only [hReservation]
          rw [EvmYul.UInt256.toNat_ofNat_of_lt hSourceM,
            EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
          exact M_mono_active hActive
        · exact hRel.returnData
        · exact hRel.output
  · rw [EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
    exact hTargetExpanded
  · rw [EvmYul.UInt256.toNat_ofNat_of_lt hTargetM]
    exact
      (show target.activeWords.toNat ≤
          EvmYul.MachineState.M target.activeWords.toNat
            expansionAddress length by
        cases length <;> simp [EvmYul.MachineState.M])
  · exact
      size_write_ge target.memory target.memory sourceAddress
        address length hHost

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
