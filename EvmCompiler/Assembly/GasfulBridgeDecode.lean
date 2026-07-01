import EvmCompiler.Assembly.GasfulBridgeTerminal

/-! Decode facts used by the recursive gasful/open frame bridge. -/

namespace EvmCompiler.Assembly.GasfulBridge

open Simulation

theorem decode_arg_eq
    {bytes : ByteArray} {pc : Nat}
    {op : EvmYul.Operation .EVM} {arg : Option (Word × Nat)}
    (hDecode :
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) = some (op, arg)) :
    arg =
      if EvmYul.EVM.argOnNBytesOfInstr op == 0 then none
      else
        some
          (EvmYul.uInt256OfByteArray
            (bytes.extract' (EvmYul.UInt256.ofNat pc).toNat.succ
              ((EvmYul.UInt256.ofNat pc).toNat.succ +
                EvmYul.EVM.argOnNBytesOfInstr op)),
            EvmYul.EVM.argOnNBytesOfInstr op) := by
  unfold EvmYul.EVM.decode at hDecode
  rcases Option.bind_eq_some_iff.mp hDecode with ⟨parsed, hParsed, hResult⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hResult
  rcases hResult with ⟨hOp, hArg⟩
  subst parsed
  exact hArg.symm

theorem PrimOp.toEVM_of_ofEVM?_stopArith
    {evmOp : EvmYul.Operation.SAOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.StopArith evmOp) = some op) :
    op.toEVM = .StopArith evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_compBit
    {evmOp : EvmYul.Operation.CBLOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.CompBit evmOp) = some op) :
    op.toEVM = .CompBit evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_keccak
    {evmOp : EvmYul.Operation.KOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.Keccak evmOp) = some op) :
    op.toEVM = .Keccak evmOp := by
  cases evmOp
  cases hOp
  rfl

theorem PrimOp.toEVM_of_ofEVM?_env
    {evmOp : EvmYul.Operation.EOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.Env evmOp) = some op) :
    op.toEVM = .Env evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_block
    {evmOp : EvmYul.Operation.BOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.Block evmOp) = some op) :
    op.toEVM = .Block evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_stackMemFlow
    {evmOp : EvmYul.Operation.SMSFOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.StackMemFlow evmOp) = some op) :
    op.toEVM = .StackMemFlow evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_dup
    {evmOp : EvmYul.Operation.DOp} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.Dup evmOp) = some op) :
    op.toEVM = .Dup evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_exchange
    {evmOp : EvmYul.Operation.ExOp} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.Exchange evmOp) = some op) :
    op.toEVM = .Exchange evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_log
    {evmOp : EvmYul.Operation.LOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.Log evmOp) = some op) :
    op.toEVM = .Log evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?_system
    {evmOp : EvmYul.Operation.SOp .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? (.System evmOp) = some op) :
    op.toEVM = .System evmOp := by
  cases evmOp <;> cases hOp <;> rfl

theorem PrimOp.toEVM_of_ofEVM?
    {evmOp : EvmYul.Operation .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? evmOp = some op) :
    op.toEVM = evmOp := by
  cases evmOp with
  | StopArith evmOp => exact PrimOp.toEVM_of_ofEVM?_stopArith hOp
  | CompBit evmOp => exact PrimOp.toEVM_of_ofEVM?_compBit hOp
  | Keccak evmOp => exact PrimOp.toEVM_of_ofEVM?_keccak hOp
  | Env evmOp => exact PrimOp.toEVM_of_ofEVM?_env hOp
  | Block evmOp => exact PrimOp.toEVM_of_ofEVM?_block hOp
  | StackMemFlow evmOp => exact PrimOp.toEVM_of_ofEVM?_stackMemFlow hOp
  | Push evmOp => cases evmOp <;> cases hOp
  | Dup evmOp => exact PrimOp.toEVM_of_ofEVM?_dup hOp
  | Exchange evmOp => exact PrimOp.toEVM_of_ofEVM?_exchange hOp
  | Log evmOp => exact PrimOp.toEVM_of_ofEVM?_log hOp
  | System evmOp => exact PrimOp.toEVM_of_ofEVM?_system hOp

theorem compact_prim_decodeAt_of_evm_decode
    {bytes : ByteArray} {pc : Nat}
    {evmOp : EvmYul.Operation .EVM} {op : PrimOp}
    (hOp : PrimOp.ofEVM? evmOp = some op)
    (hDecode :
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) =
        some (evmOp, none)) :
    Compact.decodeAt bytes pc (.prim op) := by
  refine ⟨(evmOp, none), ?_, hDecode⟩
  simp [Compact.Instr.decoded?, PrimOp.toEVM_of_ofEVM? hOp]

theorem ByteArray.extract'_size_le (bytes : ByteArray) (start stop : Nat) :
    (bytes.extract' start stop).size ≤ stop - start := by
  unfold ByteArray.extract'
  split
  · simp [ByteArray.size_extract]
    omega
  · change
      (List.take (stop - start) (List.drop start bytes.toList)).length ≤
        stop - start
    exact List.length_take_le _ _

theorem fromBytes'_lt_pow_256 (bytes : List UInt8) :
    EvmYul.fromBytes' bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [EvmYul.fromBytes']
  | cons byte rest ih =>
      rw [EvmYul.fromBytes']
      simp only [List.length_cons, pow_succ]
      have hByte : byte.toFin.val < 256 := byte.toFin.isLt
      omega

theorem uInt256OfByteArray_toNat_lt_pow_256
    (bytes : ByteArray) (width : Nat)
    (hSize : bytes.size ≤ width) (hWidth : width ≤ 32) :
    (EvmYul.uInt256OfByteArray bytes).toNat < 256 ^ width := by
  let raw := EvmYul.fromBytes' bytes.data.toList.reverse
  have hRawBase : raw < 256 ^ bytes.size := by
    simpa [raw] using fromBytes'_lt_pow_256 bytes.data.toList.reverse
  have hPowWidth : 256 ^ bytes.size ≤ 256 ^ width :=
    Nat.pow_le_pow_right (by decide : 0 < 256) hSize
  have hRawWidth : raw < 256 ^ width := lt_of_lt_of_le hRawBase hPowWidth
  have hPow32 : 256 ^ width ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by decide : 0 < 256) hWidth
  have hSizeEq : 256 ^ 32 = EvmYul.UInt256.size := by
    norm_num [EvmYul.UInt256.size]
  have hRawSize : raw < EvmYul.UInt256.size := by
    rw [← hSizeEq]
    exact lt_of_lt_of_le hRawWidth hPow32
  unfold EvmYul.uInt256OfByteArray
  rw [EvmYul.UInt256.toNat_ofNat_of_lt hRawSize]
  exact hRawWidth

theorem compact_push_decodeAt_of_evm_decode
    {bytes : ByteArray} {pc width : Nat} {value : Word}
    {evmOp : EvmYul.Operation .EVM}
    (hBounds : 0 < width ∧ width ≤ 32)
    (hOp : Compact.pushOp? width = some evmOp)
    (hDecode :
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) =
        some (evmOp, some (value, width))) :
    Compact.FitsWidth width value.toNat ∧
      Compact.decodeAt bytes pc (.push width value) := by
  have hArg := decode_arg_eq hDecode
  have hArgWidth : EvmYul.EVM.argOnNBytesOfInstr evmOp = width :=
    (Compact.pushOp?_properties hBounds hOp).2
  rw [hArgWidth] at hArg
  have hWidthNe : (width == 0) = false := by
    simp [Nat.ne_of_gt hBounds.1]
  simp [hWidthNe] at hArg
  have hValue :
      value = EvmYul.uInt256OfByteArray
        (bytes.extract' (EvmYul.UInt256.ofNat pc).toNat.succ
          ((EvmYul.UInt256.ofNat pc).toNat.succ + width)) :=
    hArg
  have hExtractSize :
      (bytes.extract' (EvmYul.UInt256.ofNat pc).toNat.succ
        ((EvmYul.UInt256.ofNat pc).toNat.succ + width)).size ≤ width := by
    have hSize := ByteArray.extract'_size_le bytes
      (EvmYul.UInt256.ofNat pc).toNat.succ
      ((EvmYul.UInt256.ofNat pc).toNat.succ + width)
    simpa using hSize
  have hFits : Compact.FitsWidth width value.toNat := by
    refine ⟨hBounds.1, hBounds.2, ?_⟩
    rw [hValue]
    exact uInt256OfByteArray_toNat_lt_pow_256 _ width
      hExtractSize hBounds.2
  exact ⟨hFits, ⟨(evmOp, some (value, width)), by
    simp [Compact.Instr.decoded?, hOp], hDecode⟩⟩

theorem exists_compact_push_of_evm_decode
    {bytes : ByteArray} {pc width : Nat} {value : Word}
    {evmOp : EvmYul.Operation .EVM}
    (hBounds : 0 < width ∧ width ≤ 32)
    (hOp : Compact.pushOp? width = some evmOp)
    (hDecode :
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) =
        some (evmOp, some (value, width))) :
    ∃ instr : Compact.Instr,
      instr.Valid ∧ Compact.decodeAt bytes pc instr := by
  obtain ⟨hFits, hAt⟩ :=
    compact_push_decodeAt_of_evm_decode hBounds hOp hDecode
  exact ⟨.push width value, hFits, hAt⟩

/-- Every successful EVMYul byte decode has a valid Compact instruction.
The only semantic mismatch left for recursive execution is therefore a decode
miss: `EVM.X` defaults `none` to `STOP`, while the open raw semantics rejects
it as an invalid instruction. -/
theorem exists_compact_instr_of_evm_decode
    {bytes : ByteArray} {pc : Nat}
    {op : EvmYul.Operation .EVM} {arg : Option (Word × Nat)}
    (hDecode :
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) = some (op, arg))
    (hNotPush0 : op ≠ EvmYul.Operation.PUSH0)
    (hNotCLZ : op ≠ EvmYul.Operation.CLZ) :
    ∃ instr : Compact.Instr,
      instr.Valid ∧ Compact.decodeAt bytes pc instr := by
  have hArg := decode_arg_eq hDecode
  cases op with
  | StopArith op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | CompBit op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        first
        | exact False.elim (hNotCLZ rfl)
        |
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | Keccak op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op
      exact ⟨.prim _, trivial,
        compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | Env op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | Block op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | StackMemFlow op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        first
        | exact ⟨.jump, trivial, ⟨_, rfl, hDecode⟩⟩
        | exact ⟨.jumpi, trivial, ⟨_, rfl, hDecode⟩⟩
        | exact ⟨.jumpdest, trivial, ⟨_, rfl, hDecode⟩⟩
        | exact ⟨.prim _, trivial,
            compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | Push op =>
      cases op <;>
        simp [EvmYul.EVM.argOnNBytesOfInstr] at hArg <;>
        subst arg
      · exact False.elim (hNotPush0 rfl)
      all_goals
        first
        | exact exists_compact_push_of_evm_decode
            (width := 1) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 2) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 3) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 4) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 5) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 6) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 7) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 8) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 9) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 10) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 11) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 12) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 13) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 14) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 15) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 16) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 17) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 18) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 19) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 20) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 21) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 22) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 23) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 24) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 25) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 26) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 27) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 28) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 29) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 30) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 31) (by omega) rfl hDecode
        | exact exists_compact_push_of_evm_decode
            (width := 32) (by omega) rfl hDecode
  | Dup op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | Exchange op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | Log op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩
  | System op =>
      have hArgNone : arg = none := by
        simpa [EvmYul.EVM.argOnNBytesOfInstr] using hArg
      subst arg
      cases op <;>
        exact ⟨.prim _, trivial,
          compact_prim_decodeAt_of_evm_decode (hOp := rfl) hDecode⟩

/-- Exact local code condition required by the recursive frame bridge.
Compiler-side reachability only has to rule out decode misses plus opcodes that
EVMYul decodes but this compact assembly layer does not model natively. -/
def SupportedDecodeAt (bytes : ByteArray) (pc : Word) : Prop :=
  ∃ op arg,
    EvmYul.EVM.decode bytes pc = some (op, arg) ∧
      op ≠ EvmYul.Operation.PUSH0 ∧
      op ≠ EvmYul.Operation.CLZ

theorem compact_decodeAt_of_supported
    {bytes : ByteArray} {pc : Word}
    (hSupported : SupportedDecodeAt bytes pc) :
    ∃ instr : Compact.Instr,
      instr.Valid ∧ Compact.decodeAt bytes pc.toNat instr := by
  rcases hSupported with ⟨op, arg, hDecode, hNotPush0, hNotCLZ⟩
  have hDecodeNat :
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc.toNat) =
        some (op, arg) := by
    simpa using hDecode
  exact exists_compact_instr_of_evm_decode hDecodeNat hNotPush0 hNotCLZ

end EvmCompiler.Assembly.GasfulBridge
