import EvmCompiler.Compiler.MemoryRelation
import EvmCompiler.Structured.Syntax

namespace EvmCompiler
namespace Simulation
namespace MemorySafety

abbrev Word := Assembly.Word

/--
A dynamic source memory range is safe for allocation lowering when it does not
overlap the compiler-owned scratch reservation. Stack-only compilation has no
reserved interval and therefore permits every source range.
-/
@[simp] abbrev RegionAllowed (contract : MemoryContract.Contract)
    (address size : Nat) : Prop :=
  match contract.scratch? with
  | none => True
  | some reservation =>
      reservation.sourceAccessAllowed address size

/--
Ordinary EVM memory states do not contain materialized bytes beyond the active
memory extent. This source-facing invariant prevents target spill allocation
from exposing dormant source bytes through a later `mload`.
-/
@[simp] abbrev MemoryConsistent (machine : EvmYul.MachineState) : Prop :=
  Compiler.MemoryRelation.MemoryConsistent machine

/--
Every memory expansion performed by a primitive remains representable by the
ordinary EVM active-word counter and its `MSIZE` byte value.
-/
@[simp] abbrev PrimitiveExpansionSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mload, [address]
  | .mstore, [address, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat MemoryContract.wordBytes
  | .mstore8, [address, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat 1
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size]
  | .extcodecopy, [_, destination, _source, size] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat
  | .mcopy, [destination, source, size] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        (max destination.toNat source.toNat) size.toNat
  | .keccak256, [address, size]
  | .log0, [address, size]
  | .log1, [address, size, _]
  | .log2, [address, size, _, _]
  | .log3, [address, size, _, _, _]
  | .log4, [address, size, _, _, _, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat size.toNat
  | _, _ => True

/--
Memory writes and finite memory reads stay inside the host byte-array address
space used by the executable semantics.
-/
@[simp] abbrev PrimitiveHostSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mstore, [address, _] =>
      address.toNat + MemoryContract.wordBytes < USize.size
  | .mstore8, [address, _] =>
      address.toNat + 1 < USize.size
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size]
  | .extcodecopy, [_, destination, _source, size] =>
      destination.toNat + size.toNat < USize.size
  | .mcopy, [destination, source, size] =>
      destination.toNat + size.toNat < USize.size ∧
        source.toNat + size.toNat < USize.size
  | .keccak256, [address, size]
  | .log0, [address, size]
  | .log1, [address, size, _]
  | .log2, [address, size, _, _]
  | .log3, [address, size, _, _, _]
  | .log4, [address, size, _, _, _, _] =>
      address.toNat + size.toNat < USize.size
  | _, _ => True

/--
Source-facing memory safety for one primitive application.

`values` follows the stack-free source argument order. Reversing it
reconstructs concrete EVM pop order. External call/create operations are
deliberately excluded from this closed-world contract.
-/
@[simp] abbrev PrimitiveMemorySafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mload, [address] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat MemoryContract.wordBytes ∧
        PrimitiveExpansionSafe op values
  | .mstore, [address, _value] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat MemoryContract.wordBytes ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .mstore8, [address, _value] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat 1 ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .extcodecopy, [_account, destination, _source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .mcopy, [destination, source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        RegionAllowed contract source.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .keccak256, [address, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .log0, [address, size]
  | .log1, [address, size, _topic0]
  | .log2, [address, size, _topic0, _topic1]
  | .log3, [address, size, _topic0, _topic1, _topic2]
  | .log4, [address, size, _topic0, _topic1, _topic2, _topic3] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .create, _
  | .call, _
  | .callcode, _
  | .delegatecall, _
  | .create2, _
  | .staticcall, _ =>
      False
  | _, _ => True

/--
A source memory window used by an open-world request or response.

Zero-length windows are safe regardless of their offset: the executable EVM
semantics reads, writes, and expands no bytes in that case. Nonempty windows
must avoid compiler scratch storage and satisfy both EVM and host bounds.
-/
def WindowSafe (contract : MemoryContract.Contract)
    (address size : Nat) : Prop :=
  size = 0 ∨
    (RegionAllowed contract address size ∧
      Compiler.MemoryRelation.ExpansionNoWrap address size ∧
      address + size < USize.size)

@[simp] theorem windowSafe_zero
    (contract : MemoryContract.Contract) (address : Nat) :
    WindowSafe contract address 0 :=
  Or.inl rfl

namespace WindowSafe

theorem expansion
    {contract : MemoryContract.Contract} {address size : Nat}
    (hSafe : WindowSafe contract address size) :
    Compiler.MemoryRelation.ExpansionNoWrap address size := by
  rcases hSafe with hZero | ⟨_hAllowed, hExpansion, _hHost⟩
  · subst size
    simp [Compiler.MemoryRelation.ExpansionNoWrap,
      EvmYul.MachineState.M]
    norm_num [EvmYul.UInt256.size]
  · exact hExpansion

theorem host_of_pos
    {contract : MemoryContract.Contract} {address size : Nat}
    (hSafe : WindowSafe contract address size) (hPos : 0 < size) :
    address + size < USize.size := by
  rcases hSafe with hZero | ⟨_hAllowed, _hExpansion, hHost⟩
  · omega
  · exact hHost

theorem allowed_of_pos
    {contract : MemoryContract.Contract} {address size : Nat}
    (hSafe : WindowSafe contract address size) (hPos : 0 < size) :
    RegionAllowed contract address size := by
  rcases hSafe with hZero | ⟨hAllowed, _hExpansion, _hHost⟩
  · omega
  · exact hAllowed

end WindowSafe

/-- Related machines expose identical bytes through every safe source window. -/
theorem readWithPadding_eq_of_windowSafe
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : Compiler.MemoryRelation.MachineRel contract source target)
    (address size : Nat)
    (hSafe : WindowSafe contract address size) :
    source.memory.readWithPadding address size =
      target.memory.readWithPadding address size := by
  rcases hSafe with hZero | ⟨hAllowed, _hExpansion, hHost⟩
  · subst size
    simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding]
  · cases hReservation : contract.scratch? with
    | none =>
        have hMemory : source.memory = target.memory := by
          simpa [hReservation] using hRel.memory
        rw [hMemory]
    | some reservation =>
        have hMemory :
            Compiler.MemoryRelation.OutsideReservation
              reservation source.memory target.memory := by
          simpa [hReservation] using hRel.memory
        have hAllowed' :
            reservation.sourceAccessAllowed address size := by
          simpa [hReservation] using hAllowed
        exact
          Compiler.MemoryRelation.OutsideReservation.readWithPadding
            hMemory address size hAllowed' (by omega)

/--
Finishing the same external response preserves the compiler memory relation.
The response bytes are arbitrary; only the caller-owned input/output windows
are constrained.
-/
theorem finishExternalCall_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : Compiler.MemoryRelation.MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (returnData : ByteArray)
    (inputOffset inputSize outputOffset outputSize : Word)
    (hInput : WindowSafe contract inputOffset.toNat inputSize.toNat)
    (hOutput : WindowSafe contract outputOffset.toNat outputSize.toNat) :
    Compiler.MemoryRelation.MachineRel contract
      (source.finishExternalCall returnData
        inputOffset inputSize outputOffset outputSize)
      (target.finishExternalCall returnData
        inputOffset inputSize outputOffset outputSize) := by
  let sourceInputWords :=
    EvmYul.MachineState.M source.activeWords.toNat
      inputOffset.toNat inputSize.toNat
  let targetInputWords :=
    EvmYul.MachineState.M target.activeWords.toNat
      inputOffset.toNat inputSize.toNat
  let sourceFinalWords :=
    EvmYul.MachineState.M sourceInputWords
      outputOffset.toNat outputSize.toNat
  let targetFinalWords :=
    EvmYul.MachineState.M targetInputWords
      outputOffset.toNat outputSize.toNat
  let copyLen := min outputSize.toNat returnData.size
  have hInputExpansion := hInput.expansion
  have hOutputExpansion := hOutput.expansion
  have hTargetInputBytes :
      targetInputWords * MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    exact
      Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
        hTargetNoWrap hInputExpansion
  have hTargetFinalBytes :
      targetFinalWords * MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    exact
      Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
        hTargetInputBytes hOutputExpansion
  have hTargetInputLt : targetInputWords < EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  have hTargetFinalLt : targetFinalWords < EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  cases hReservation : contract.scratch? with
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
        simp [EvmYul.MachineState.finishExternalCall,
          EvmYul.writeBytes, hMemory]
      · rw [hReservation]
        simp [EvmYul.MachineState.finishExternalCall,
          EvmYul.writeBytes, hActive]
      · simp [EvmYul.MachineState.finishExternalCall]
      · simp [EvmYul.MachineState.finishExternalCall]

  | some reservation =>
      have hMemory :
          Compiler.MemoryRelation.OutsideReservation
            reservation source.memory target.memory := by
        simpa [hReservation] using hRel.memory
      have hActive :
          source.activeWords.toNat ≤ target.activeWords.toNat := by
        simpa [hReservation] using hRel.activeWords
      have hSourceNoWrap :
          source.activeWords.toNat * MemoryContract.wordBytes <
            EvmYul.UInt256.size :=
        lt_of_le_of_lt
          (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
          hTargetNoWrap
      have hSourceInputBytes :
          sourceInputWords * MemoryContract.wordBytes <
            EvmYul.UInt256.size := by
        exact
          Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
            hSourceNoWrap hInputExpansion
      have hSourceFinalBytes :
          sourceFinalWords * MemoryContract.wordBytes <
            EvmYul.UInt256.size := by
        exact
          Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
            hSourceInputBytes hOutputExpansion
      have hSourceFinalLt : sourceFinalWords < EvmYul.UInt256.size := by
        have hPositive : 0 < MemoryContract.wordBytes := by decide
        nlinarith
      refine
        { memory := ?_
          activeWords := ?_
          returnData := ?_
          output := ?_ }
      · rw [hReservation]
        by_cases hOutputZero : outputSize.toNat = 0
        ·
            simpa [EvmYul.MachineState.finishExternalCall,
              EvmYul.writeBytes, copyLen, hOutputZero] using hMemory
        ·
            have hOutputPos : 0 < outputSize.toNat :=
              Nat.pos_of_ne_zero hOutputZero
            have hHost :
                outputOffset.toNat + outputSize.toNat < USize.size :=
              hOutput.host_of_pos hOutputPos
            have hCopyLe : copyLen ≤ outputSize.toNat := by
              exact min_le_left _ _
            have hCopyHost :
                outputOffset.toNat + copyLen < USize.size := by
              omega
            have hWritten :=
              Compiler.MemoryRelation.OutsideReservation.write_both
                returnData 0 outputOffset.toNat copyLen hMemory hCopyHost
            simpa [EvmYul.MachineState.finishExternalCall,
              EvmYul.writeBytes, copyLen] using hWritten
      · simp only [hReservation]
        simp only [EvmYul.MachineState.finishExternalCall,
          EvmYul.writeBytes]
        change
          (EvmYul.UInt256.ofNat sourceFinalWords).toNat ≤
            (EvmYul.UInt256.ofNat targetFinalWords).toNat
        rw [EvmYul.UInt256.toNat_ofNat_of_lt hSourceFinalLt,
          EvmYul.UInt256.toNat_ofNat_of_lt hTargetFinalLt]
        exact
          Compiler.MemoryRelation.M_mono_active
            (Compiler.MemoryRelation.M_mono_active hActive)
      · simp [EvmYul.MachineState.finishExternalCall]
      · simp [EvmYul.MachineState.finishExternalCall]

/-- Growth facts for one concrete external-response installation. -/
structure FinishExternalGrowth
    (before after : EvmYul.MachineState) : Prop where
  memory : before.memory.size ≤ after.memory.size
  active : before.activeWords.toNat ≤ after.activeWords.toNat
  activeNoWrap :
    after.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

theorem finishExternalCall_growth
    {contract : MemoryContract.Contract}
    (before : EvmYul.MachineState)
    (hBeforeNoWrap :
      before.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (returnData : ByteArray)
    (inputOffset inputSize outputOffset outputSize : Word)
    (hInput : WindowSafe contract inputOffset.toNat inputSize.toNat)
    (hOutput : WindowSafe contract outputOffset.toNat outputSize.toNat) :
    FinishExternalGrowth before
      (before.finishExternalCall returnData
        inputOffset inputSize outputOffset outputSize) := by
  let inputWords :=
    EvmYul.MachineState.M before.activeWords.toNat
      inputOffset.toNat inputSize.toNat
  let finalWords :=
    EvmYul.MachineState.M inputWords
      outputOffset.toNat outputSize.toNat
  let copyLen := min outputSize.toNat returnData.size
  have hInputNoWrap :
      inputWords * MemoryContract.wordBytes < EvmYul.UInt256.size :=
    Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
      hBeforeNoWrap hInput.expansion
  have hFinalNoWrap :
      finalWords * MemoryContract.wordBytes < EvmYul.UInt256.size :=
    Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
      hInputNoWrap hOutput.expansion
  have hFinalLt : finalWords < EvmYul.UInt256.size := by
    have hPositive : 0 < MemoryContract.wordBytes := by decide
    nlinarith
  have hInputMono : before.activeWords.toNat ≤ inputWords := by
    dsimp [inputWords]
    cases hSize : inputSize.toNat with
    | zero => simp [EvmYul.MachineState.M, hSize]
    | succ size =>
        simp only [EvmYul.MachineState.M]
        exact Nat.le_max_left _ _
  have hFinalMono : inputWords ≤ finalWords := by
    dsimp [finalWords]
    cases hSize : outputSize.toNat with
    | zero => simp [EvmYul.MachineState.M, hSize]
    | succ size =>
        simp only [EvmYul.MachineState.M]
        exact Nat.le_max_left _ _
  refine ⟨?_, ?_, ?_⟩
  · by_cases hOutputZero : outputSize.toNat = 0
    · simp [EvmYul.MachineState.finishExternalCall,
        EvmYul.writeBytes, ByteArray.write, copyLen, hOutputZero]
    · have hOutputPos : 0 < outputSize.toNat :=
        Nat.pos_of_ne_zero hOutputZero
      have hHost := hOutput.host_of_pos hOutputPos
      have hCopyLe : copyLen ≤ outputSize.toNat := min_le_left _ _
      have hCopyHost : outputOffset.toNat + copyLen < USize.size := by
        omega
      simpa [EvmYul.MachineState.finishExternalCall,
        EvmYul.writeBytes, copyLen] using
        Compiler.MemoryRelation.size_write_ge
          returnData before.memory 0 outputOffset.toNat copyLen hCopyHost
  · simp only [EvmYul.MachineState.finishExternalCall,
      EvmYul.writeBytes]
    change before.activeWords.toNat ≤
      (EvmYul.UInt256.ofNat finalWords).toNat
    rw [EvmYul.UInt256.toNat_ofNat_of_lt hFinalLt]
    exact hInputMono.trans hFinalMono
  · simp only [EvmYul.MachineState.finishExternalCall,
      EvmYul.writeBytes]
    change
      (EvmYul.UInt256.ofNat finalWords).toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size
    rw [EvmYul.UInt256.toNat_ofNat_of_lt hFinalLt]
    exact hFinalNoWrap

/-- A safe response copy cannot change a compiler-reserved scratch word. -/
theorem lookupMemory_finishExternalCall_of_reserved
    {contract : MemoryContract.Contract}
    {reservation : MemoryContract.ScratchReservation}
    (before : EvmYul.MachineState)
    (hBeforeNoWrap :
      before.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (returnData : ByteArray)
    (inputOffset inputSize outputOffset outputSize : Word)
    (hInput : WindowSafe contract inputOffset.toNat inputSize.toNat)
    (hOutput : WindowSafe contract outputOffset.toNat outputSize.toNat)
    (query : Nat)
    (hReservation : contract.scratch? = some reservation)
    (hReserved : reservation.containsRegion query 1)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤ before.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        before.activeWords.toNat * MemoryContract.wordBytes) :
    (before.finishExternalCall returnData
        inputOffset inputSize outputOffset outputSize).lookupMemory
          (EvmYul.UInt256.ofNat query) =
      before.lookupMemory (EvmYul.UInt256.ofNat query) := by
  let after := before.finishExternalCall returnData
    inputOffset inputSize outputOffset outputSize
  have hGrowth : FinishExternalGrowth before after :=
    finishExternalCall_growth before hBeforeNoWrap returnData
      inputOffset inputSize outputOffset outputSize hInput hOutput
  have hQueryLt : query < EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hBeforeNoWrap)
  have hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  by_cases hOutputZero : outputSize.toNat = 0
  · have hMemory : after.memory = before.memory := by
      simp [after, EvmYul.MachineState.finishExternalCall,
        EvmYul.writeBytes, ByteArray.write, hOutputZero]
    exact
      Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
        query hQuery hMemory hGrowth.active hBeforeNoWrap
        hGrowth.activeNoWrap hReadMemory hReadActive
  · have hOutputPos : 0 < outputSize.toNat :=
      Nat.pos_of_ne_zero hOutputZero
    have hHost := hOutput.host_of_pos hOutputPos
    have hAllowed :
        reservation.sourceAccessAllowed
          outputOffset.toNat outputSize.toNat := by
      simpa [RegionAllowed, hReservation] using
        hOutput.allowed_of_pos hOutputPos
    let copyLen := min outputSize.toNat returnData.size
    have hCopyLe : copyLen ≤ outputSize.toNat := min_le_left _ _
    have hCopyHost : outputOffset.toNat + copyLen < USize.size := by
      omega
    have hReservedStart : reservation.base ≤ query := hReserved.1
    have hReservedEnd :
        query + MemoryContract.wordBytes ≤ reservation.endExclusive := by
      simpa using hReserved.2
    have hDisjoint :
        query + MemoryContract.wordBytes ≤ outputOffset.toNat ∨
          outputOffset.toNat + copyLen ≤ query := by
      rcases hAllowed with hBefore | hAfter
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hMemory :
        after.memory =
          returnData.write 0 before.memory outputOffset.toNat copyLen := by
      rfl
    exact
      Compiler.MemoryRelation.lookupMemory_eq_of_write_disjoint_growing
        returnData before after 0 outputOffset.toNat copyLen query
        hCopyHost hMemory hQuery hReadMemory hReadActive
        hBeforeNoWrap hGrowth.active hGrowth.activeNoWrap hDisjoint

/--
Source-facing primitive safety for the open interaction semantics.

CALL-family requests read calldata and may write returndata. CREATE-family
requests read init code. The concrete gas operand is intentionally irrelevant
to this memory contract. Every nonexternal operation keeps the established
`PrimitiveMemorySafe` contract.
-/
def OpenPrimitiveMemorySafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .call, [_gas, _address, _value,
      inputOffset, inputSize, outputOffset, outputSize]
  | .callcode, [_gas, _address, _value,
      inputOffset, inputSize, outputOffset, outputSize] =>
      MemoryConsistent machine ∧
        WindowSafe contract inputOffset.toNat inputSize.toNat ∧
        WindowSafe contract outputOffset.toNat outputSize.toNat
  | .delegatecall, [_gas, _address,
      inputOffset, inputSize, outputOffset, outputSize]
  | .staticcall, [_gas, _address,
      inputOffset, inputSize, outputOffset, outputSize] =>
      MemoryConsistent machine ∧
        WindowSafe contract inputOffset.toNat inputSize.toNat ∧
        WindowSafe contract outputOffset.toNat outputSize.toNat
  | .create, [_value, initOffset, initSize]
  | .create2, [_value, initOffset, initSize, _salt] =>
      MemoryConsistent machine ∧
        WindowSafe contract initOffset.toNat initSize.toNat
  | _, _ => PrimitiveMemorySafe contract op machine values

@[simp] theorem openPrimitiveMemorySafe_call_zero_windows
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState)
    (gas address value inputOffset outputOffset : Word)
    (hConsistent : MemoryConsistent machine) :
    OpenPrimitiveMemorySafe contract .call machine
      [EvmYul.UInt256.ofNat 0, outputOffset,
        EvmYul.UInt256.ofNat 0, inputOffset, value, address, gas] := by
  change
    MemoryConsistent machine ∧
      WindowSafe contract inputOffset.toNat 0 ∧
      WindowSafe contract outputOffset.toNat 0
  exact
    ⟨hConsistent, windowSafe_zero contract inputOffset.toNat,
      windowSafe_zero contract outputOffset.toNat⟩

@[simp] theorem openPrimitiveMemorySafe_create_zero_window
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState)
    (value initOffset : Word)
    (hConsistent : MemoryConsistent machine) :
    OpenPrimitiveMemorySafe contract .create machine
      [EvmYul.UInt256.ofNat 0, initOffset, value] := by
  change
    MemoryConsistent machine ∧
      WindowSafe contract initOffset.toNat 0
  exact ⟨hConsistent, windowSafe_zero contract initOffset.toNat⟩

theorem noExternal_of_primitiveMemorySafe
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    {machine : EvmYul.MachineState} {values : List Word}
    (hSafe : PrimitiveMemorySafe contract op machine values) :
    op.toPrimOp.isExternalCallCreate = false := by
  cases op <;>
    simp [PrimitiveMemorySafe, Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isExternalCallCreate] at hSafe ⊢

/--
Terminal source memory reads obey the same reservation contract. `RETURN` and
`REVERT` read a byte range; `STOP` and `SELFDESTRUCT` do not read memory.
-/
@[simp] abbrev TerminalMemorySafe (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind) (values : List Word) : Prop :=
  match kind, values.reverse with
  | .return, [address, size]
  | .revert, [address, size] =>
      RegionAllowed contract address.toNat size.toNat ∧
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat size.toNat ∧
        address.toNat + size.toNat < USize.size
  | .stop, []
  | .selfdestruct, [_recipient] =>
      True
  | _, _ => False

@[simp] theorem regionAllowed_unrestricted (address size : Nat) :
    RegionAllowed MemoryContract.unrestricted address size := by
  simp [RegionAllowed, MemoryContract.unrestricted]

theorem primitiveMemorySafe_unrestricted_of_noExternal
    {op : Structured.BasicOp} {machine : EvmYul.MachineState}
    {values : List Word}
    (hNoExternal : op.toPrimOp.isExternalCallCreate = false) :
    MemoryConsistent machine →
      PrimitiveExpansionSafe op values →
      PrimitiveHostSafe op values →
      PrimitiveMemorySafe MemoryContract.unrestricted op machine values := by
  intro hConsistent hExpansion hHost
  unfold PrimitiveMemorySafe
  simp only [RegionAllowed, MemoryContract.unrestricted]
  split <;>
    simp_all [MemoryConsistent, PrimitiveExpansionSafe, PrimitiveHostSafe,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isExternalCallCreate]

@[simp] theorem primitiveMemorySafe_gas
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .gas machine [] := by
  simp [PrimitiveMemorySafe]

@[simp] theorem primitiveMemorySafe_msize
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .msize machine [] := by
  simp [PrimitiveMemorySafe]

@[simp] theorem terminalMemorySafe_stop
    (contract : MemoryContract.Contract) :
    TerminalMemorySafe contract .stop [] := by
  simp [TerminalMemorySafe]

@[simp] theorem terminalMemorySafe_selfdestruct
    (contract : MemoryContract.Contract) (recipient : Word) :
    TerminalMemorySafe contract .selfdestruct [recipient] := by
  simp [TerminalMemorySafe]

end MemorySafety
end Simulation
end EvmCompiler
