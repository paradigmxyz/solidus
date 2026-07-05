import EvmCompiler.Assembly.Compact

/-!
# Verified jumpdest-scan membership for compact programs

EVMYulLean's charged interpreter `EvmYul.EVM.X` validates every `JUMP`/`JUMPI`
target against the jumpdest table `EvmYul.EVM.D_J code 0`.  With the scanner's
auxiliary recursion `D_J_aux` total (Nat-indexed, `termination_by
c.size - n`) and equipped with unfolding lemmas, this module proves the
compiler-facing membership fact: every located `.jumpdest` of a well-formed
compact program is listed by the scanner over ANY byte image that decodes the
program at its located PCs -- in particular over `encode program ++ payload ++
constructor-argument suffix`, because `Compact.DecodingCorrect` is itself
suffix-tolerant.

The argument follows the scan left to right along the program's
`codeLayoutFrom` layout: at each located PC the decode fact pins the parsed
opcode and its immediate width, so the scanner's skip lands exactly on the
next located PC; a located `.jumpdest` therefore gets pushed into the
accumulator, and accumulator membership is monotone along the rest of the
scan.
-/

namespace EvmCompiler
namespace Assembly
namespace Compact

open EvmYul

theorem uint256_beq_refl (x : EvmYul.UInt256) : (x == x) = true := by
  cases x with
  | mk v => exact beq_self_eq_true v

theorem array_contains_push_self (result : Array EvmYul.UInt256)
    (x : EvmYul.UInt256) : (result.push x).contains x = true := by
  simp [Array.contains, uint256_beq_refl]

theorem array_contains_push_mono (result : Array EvmYul.UInt256)
    (x y : EvmYul.UInt256) (h : result.contains x = true) :
    (result.push y).contains x = true := by
  simp [Array.contains] at h ⊢
  exact Or.inl h

/-- Accumulator monotonicity of the jumpdest scanner. -/
theorem D_J_aux_contains_mono (c : ByteArray) (n : Nat)
    (result : Array EvmYul.UInt256) (x : EvmYul.UInt256)
    (h : result.contains x = true) :
    (EvmYul.EVM.D_J_aux c n result).contains x = true := by
  by_cases hlt : n < c.size
  · rw [EvmYul.EVM.D_J_aux_step c n result hlt]
    cases hParse : EvmYul.EVM.parseInstr c[n] with
    | none => exact h
    | some ci =>
        simp only
        by_cases hDest : ci = EvmYul.Operation.JUMPDEST
        · rw [if_pos hDest]
          exact D_J_aux_contains_mono c
            (n + 1 + EvmYul.EVM.argOnNBytesOfInstr ci)
            (result.push (.ofNat n)) x
            (array_contains_push_mono result x _ h)
        · rw [if_neg hDest]
          exact D_J_aux_contains_mono c
            (n + 1 + EvmYul.EVM.argOnNBytesOfInstr ci) result x h
  · rw [EvmYul.EVM.D_J_aux_out_of_bounds c n result hlt]
    exact h
  termination_by c.size - n
  decreasing_by all_goals omega

/-- Unpack a `decodeAt` fact into a scanner-shaped parse fact. -/
theorem parse_of_decodeAt
    {bytes : ByteArray} {pc : Nat} {instr : Instr}
    (hDecode : decodeAt bytes pc instr)
    (hPcNat : (EvmYul.UInt256.ofNat pc).toNat = pc) :
    ∃ (_ : pc < bytes.size) (op : EvmYul.Operation .EVM),
      EvmYul.EVM.parseInstr bytes[pc] = some op ∧
      1 + EvmYul.EVM.argOnNBytesOfInstr op = instr.byteSize ∧
      (instr = .jumpdest → op = EvmYul.Operation.JUMPDEST) := by
  obtain ⟨decoded, hDecoded, hDec⟩ := hDecode
  unfold EvmYul.EVM.decode at hDec
  rw [hPcNat] at hDec
  cases hGet : bytes.get? pc with
  | none => rw [hGet] at hDec; simp at hDec
  | some b =>
      rw [hGet] at hDec
      have hBind : (some b >>= EvmYul.EVM.parseInstr) =
          EvmYul.EVM.parseInstr b := rfl
      rw [hBind] at hDec
      cases hParse : EvmYul.EVM.parseInstr b with
      | none =>
          rw [hParse] at hDec
          simp at hDec
      | some op =>
          rw [hParse] at hDec
          simp at hDec
          obtain ⟨hSize, hAt⟩ : ∃ (h : pc < bytes.size), bytes[pc] = b := by
            unfold ByteArray.get? at hGet
            split at hGet
            · next hlt =>
                refine ⟨hlt, ?_⟩
                cases hGet
                rfl
            · cases hGet
          refine ⟨hSize, op, by rw [hAt]; exact hParse, ?_, ?_⟩
          · -- byteSize alignment
            cases instr with
            | push width value =>
                cases hOp : pushOp? width with
                | none => simp [Instr.decoded?, hOp] at hDecoded
                | some op' =>
                    simp [Instr.decoded?, hOp] at hDecoded
                    rw [← hDecoded] at hDec
                    by_cases hZero : EvmYul.EVM.argOnNBytesOfInstr op = 0
                    · simp [hZero] at hDec
                    · simp [hZero] at hDec
                      obtain ⟨hOpEq, -, hWidth⟩ := hDec
                      simp [Instr.byteSize]
                      omega
            | jump =>
                simp [Instr.decoded?] at hDecoded
                rw [← hDecoded] at hDec
                by_cases hZero : EvmYul.EVM.argOnNBytesOfInstr op = 0
                · simp [hZero] at hDec
                  simp [Instr.byteSize, hZero]
                · simp [hZero] at hDec
            | jumpi =>
                simp [Instr.decoded?] at hDecoded
                rw [← hDecoded] at hDec
                by_cases hZero : EvmYul.EVM.argOnNBytesOfInstr op = 0
                · simp [hZero] at hDec
                  simp [Instr.byteSize, hZero]
                · simp [hZero] at hDec
            | jumpdest =>
                simp [Instr.decoded?] at hDecoded
                rw [← hDecoded] at hDec
                by_cases hZero : EvmYul.EVM.argOnNBytesOfInstr op = 0
                · simp [hZero] at hDec
                  simp [Instr.byteSize, hZero]
                · simp [hZero] at hDec
            | prim p =>
                simp [Instr.decoded?] at hDecoded
                rw [← hDecoded] at hDec
                by_cases hZero : EvmYul.EVM.argOnNBytesOfInstr op = 0
                · simp [hZero] at hDec
                  simp [Instr.byteSize, hZero]
                · simp [hZero] at hDec
          · -- jumpdest label
            intro hInstr
            subst hInstr
            simp [Instr.decoded?] at hDecoded
            rw [← hDecoded] at hDec
            by_cases hZero : EvmYul.EVM.argOnNBytesOfInstr op = 0
            · simp [hZero] at hDec
              exact hDec
            · simp [hZero] at hDec

/-- Every located `JUMPDEST` of a laid-out, decodable code list is recorded
by the jumpdest scanner started at the list's base offset. -/
theorem D_J_aux_contains_of_layout
    {bytes : ByteArray} {code : List Located} {base : Nat}
    (hLayout : Program.codeLayoutFrom code base)
    (hDecode : ∀ located, located ∈ code →
      decodeAt bytes located.pc located.instr)
    (hPcNat : ∀ located, located ∈ code →
      (EvmYul.UInt256.ofNat located.pc).toNat = located.pc)
    (result : Array EvmYul.UInt256)
    {located : Located}
    (hMem : located ∈ code)
    (hJumpdest : located.instr = .jumpdest) :
    (EvmYul.EVM.D_J_aux bytes base result).contains
      (EvmYul.UInt256.ofNat located.pc) = true := by
  induction code generalizing base result with
  | nil => cases hMem
  | cons head rest ih =>
      obtain ⟨hHeadPc, hRestLayout⟩ := hLayout
      subst hHeadPc
      obtain ⟨hSize, op, hParse, hWidth, hDest⟩ :=
        parse_of_decodeAt (hDecode head (by simp)) (hPcNat head (by simp))
      rw [EvmYul.EVM.D_J_aux_step bytes head.pc result hSize, hParse]
      simp only
      have hIdx : head.pc + 1 + EvmYul.EVM.argOnNBytesOfInstr op =
          head.pc + head.instr.byteSize := by omega
      rw [hIdx]
      cases hMem with
      | head =>
          rw [if_pos (hDest hJumpdest)]
          exact D_J_aux_contains_mono bytes _ _ _
            (array_contains_push_self result _)
      | tail _ hRest =>
          by_cases hOpDest : op = EvmYul.Operation.JUMPDEST
          · rw [if_pos hOpDest]
            exact ih hRestLayout
              (fun item hItem => hDecode item (by simp [hItem]))
              (fun item hItem => hPcNat item (by simp [hItem]))
              _ hRest
          · rw [if_neg hOpDest]
            exact ih hRestLayout
              (fun item hItem => hDecode item (by simp [hItem]))
              (fun item hItem => hPcNat item (by simp [hItem]))
              _ hRest

/-- Every located `JUMPDEST` of a well-formed compact program is listed by
EVMYulLean's jumpdest scanner over any byte image that decodes the program
(object payloads and appended constructor arguments included). -/
theorem D_J_contains_of_decodingCorrect
    {program : Program} {bytes : ByteArray}
    (hLayout : Program.codeLayoutFrom program.code 0)
    (hWindow :
      Program.codeByteLength program.code < 18446744073709551616)
    (hDecode : DecodingCorrect program bytes)
    {located : Located}
    (hMem : located ∈ program.code)
    (hJumpdest : located.instr = .jumpdest) :
    (EvmYul.EVM.D_J bytes (EvmYul.UInt256.ofNat 0)).contains
      (EvmYul.UInt256.ofNat located.pc) = true := by
  rw [EvmYul.EVM.D_J_def]
  have h0 : (EvmYul.UInt256.ofNat 0).toNat = 0 := rfl
  rw [h0]
  exact D_J_aux_contains_of_layout hLayout hDecode.decodes
    (fun item hItem => by
      have hItemEnd := codeLayoutMemberEndLe hLayout item hItem
      have hItemSize := Instr.byteSize_pos item.instr
      exact Bytecode.uint256_ofNat_toNat_of_decode_window (by omega))
    #[] hMem hJumpdest

end Compact
end Assembly
end EvmCompiler
