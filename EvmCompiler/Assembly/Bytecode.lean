import EvmCompiler.Assembly.Preservation
import EvmYul.EVM.Semantics

namespace EvmCompiler
namespace Assembly

namespace Bytecode

/--
ByteArray constructor used by the verified encoder.

It avoids making the source compiler depend on byte parsing: the source path
ends at the labeled assembly AST.  This file is only the deployable-code bridge
from resolved assembly to EVM bytecode.
-/
def ofList (bytes : List UInt8) : ByteArray :=
  ⟨bytes.toArray⟩

def toBytesLE : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: toBytesLE width (value / 256)

def encodeWord32 (value : Word) : List UInt8 :=
  (toBytesLE 32 value.toNat).reverse

def encodeInstr : TargetInstr → List UInt8
  | .push32 value =>
      EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 :: encodeWord32 value
  | .jump =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.JUMP]
  | .jumpi =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.JUMPI]
  | .jumpdest =>
      [EvmYul.EVM.serializeInstr EvmYul.Operation.JUMPDEST]
  | .prim op =>
      [EvmYul.EVM.serializeInstr op.toEVM]

def byteSize : TargetInstr → Nat
  | .push32 _ => 33
  | .jump | .jumpi | .jumpdest | .prim _ => 1

def encodeLocated (located : LocatedTarget) : List UInt8 :=
  encodeInstr located.instr

def encodeTargetBytesRev : List LocatedTarget → List UInt8 → List UInt8
  | [], acc => acc.reverse
  | located :: rest, acc =>
      encodeTargetBytesRev rest ((encodeLocated located).reverse ++ acc)

def encodeTargetFast (target : TargetProgram) : ByteArray :=
  ofList (encodeTargetBytesRev target.code [])

@[implemented_by encodeTargetFast]
def encodeTarget (target : TargetProgram) : ByteArray :=
  ofList (target.code.flatMap encodeLocated)

private theorem encodeTargetBytesRev_eq
    (code : List LocatedTarget) (acc : List UInt8) :
    encodeTargetBytesRev code acc =
      acc.reverse ++ code.flatMap encodeLocated := by
  induction code generalizing acc with
  | nil => simp [encodeTargetBytesRev]
  | cons located rest ih =>
      simp [encodeTargetBytesRev, ih, List.reverse_append,
        List.append_assoc]

theorem encodeTargetFast_eq (target : TargetProgram) :
    encodeTargetFast target = encodeTarget target := by
  simp [encodeTargetFast, encodeTarget, encodeTargetBytesRev_eq]

def codeByteLengthFast (code : List LocatedTarget) : Nat :=
  code.foldl (fun total located => total + byteSize located.instr) 0

@[implemented_by codeByteLengthFast]
def codeByteLength : List LocatedTarget → Nat
  | [] => 0
  | located :: rest => byteSize located.instr + codeByteLength rest

private theorem foldl_byteSize_eq (code : List LocatedTarget) (total : Nat) :
    code.foldl (fun acc located => acc + byteSize located.instr) total =
      total + codeByteLength code := by
  induction code generalizing total with
  | nil => simp [codeByteLength]
  | cons located rest ih =>
      simp only [List.foldl_cons, codeByteLength]
      rw [ih]
      omega

theorem codeByteLengthFast_eq (code : List LocatedTarget) :
    codeByteLengthFast code = codeByteLength code := by
  simp [codeByteLengthFast, foldl_byteSize_eq]

theorem codeByteLength_append (left right : List LocatedTarget) :
    codeByteLength (left ++ right) =
      codeByteLength left + codeByteLength right := by
  induction left with
  | nil =>
      simp [codeByteLength]
  | cons located rest ih =>
      simp [codeByteLength, ih, Nat.add_assoc]

def codeLayoutFrom : List LocatedTarget → Nat → Prop
  | [], _ => True
  | located :: rest, pc =>
      located.pc = pc ∧ codeLayoutFrom rest (pc + byteSize located.instr)

def compileBytes? (program : Program) : Option ByteArray := do
  let target ← compile? program
  some (encodeTarget target)

def decodeAt (bytes : ByteArray) (pc : Nat) (instr : TargetInstr) : Prop :=
  EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) =
    some (instr.op, instr.arg)

def jumpdestListed? (bytes : ByteArray) (pc : Nat) : Bool :=
  (EvmYul.EVM.D_J bytes (EvmYul.UInt256.ofNat 0)).contains
      (EvmYul.UInt256.ofNat pc)

def jumpdestListed (bytes : ByteArray) (pc : Nat) : Prop :=
  jumpdestListed? bytes pc = true

/--
The byte-level facts needed to connect the AST-level compiler theorem to
EVMYulLean's bytecode decoder/fetcher.

These are deliberately not a bytecode parser.  They are the proof obligations
for the one-way encoder: the bytes emitted by `encodeTarget` decode at each
located program counter to the target instruction that the AST theorem already
uses, and EVMYul's jumpdest scanner sees every emitted `JUMPDEST`.
-/
structure EncodingCorrect (target : TargetProgram) (bytes : ByteArray) : Prop where
  bytes_eq : bytes = encodeTarget target
  decodes :
    ∀ located, located ∈ target.code → decodeAt bytes located.pc located.instr
  jumpdests :
    ∀ located,
      located ∈ target.code →
        located.instr = TargetInstr.jumpdest →
          jumpdestListed bytes located.pc

/-- The byte-level fact needed by instruction execution. Unlike
`EncodingCorrect`, this permits an object/data payload after the encoded code
prefix. -/
structure DecodingCorrect (target : TargetProgram) (bytes : ByteArray) : Prop where
  decodes :
    ∀ located, located ∈ target.code →
      decodeAt bytes located.pc located.instr

theorem EncodingCorrect.decodingCorrect
    {target : TargetProgram} {bytes : ByteArray}
    (hCorrect : EncodingCorrect target bytes) :
    DecodingCorrect target bytes where
  decodes := hCorrect.decodes

structure DecodeSafety (target : TargetProgram) : Prop where
  pcNoWrap :
    ∀ located, located ∈ target.code →
      (EvmYul.UInt256.ofNat located.pc).toNat = located.pc
  extractStartSmall :
    ∀ located, located ∈ target.code →
      located.pc + 1 < 18446744073709551616
  extractEndSmall :
    ∀ located, located ∈ target.code →
      located.pc + byteSize located.instr < 18446744073709551616

/--
Resource bound for the imported EVM decoder bridge.

The compiler constructs instruction PCs and widths. The remaining decoder
resource condition is that the generated byte stream fits in the finite
extraction window used by the imported EVMYulLean bytecode decoder.
-/
def TargetFitsDecodeWindow (target : TargetProgram) : Prop :=
  codeByteLength target.code < 18446744073709551616

/--
Assumption boundary for EVMYulLean's jumpdest scanner.

`EvmYul.EVM.D_J_aux` is opaque in the imported library, so this project can
state and use the exact scanner property needed by `X`, but cannot currently
derive it by unfolding `D_J`.
-/
structure JumpdestCorrect (target : TargetProgram) : Prop where
  jumpdests :
    ∀ located,
      located ∈ target.code →
        located.instr = TargetInstr.jumpdest →
          jumpdestListed (encodeTarget target) located.pc

def targetFitsDecodeWindow? (target : TargetProgram) : Bool :=
  decide (codeByteLength target.code < 18446744073709551616)

def jumpdestCorrect? (target : TargetProgram) : Bool :=
  target.code.all fun located =>
    if located.instr = TargetInstr.jumpdest then
      jumpdestListed? (encodeTarget target) located.pc
    else
      true

def bytecodeBridgeChecked? (target : TargetProgram) : Bool :=
  targetFitsDecodeWindow? target && jumpdestCorrect? target

theorem targetFitsDecodeWindow_of_check {target : TargetProgram}
    (hCheck : targetFitsDecodeWindow? target = true) :
    TargetFitsDecodeWindow target := by
  unfold TargetFitsDecodeWindow
  exact of_decide_eq_true (by simpa [targetFitsDecodeWindow?] using hCheck)

theorem jumpdestCorrect_of_check {target : TargetProgram}
    (hCheck : jumpdestCorrect? target = true) :
    JumpdestCorrect target where
  jumpdests := by
    intro located hMem hInstr
    have hLocated :=
      (List.all_eq_true.mp hCheck) located hMem
    simpa [jumpdestCorrect?, jumpdestListed, hInstr] using hLocated

theorem targetFitsDecodeWindow_of_bytecodeBridgeChecked
    {target : TargetProgram}
    (hCheck : bytecodeBridgeChecked? target = true) :
    TargetFitsDecodeWindow target := by
  unfold bytecodeBridgeChecked? at hCheck
  cases hWindow : targetFitsDecodeWindow? target <;> simp [hWindow] at hCheck
  exact targetFitsDecodeWindow_of_check hWindow

theorem jumpdestCorrect_of_bytecodeBridgeChecked {target : TargetProgram}
    (hCheck : bytecodeBridgeChecked? target = true) :
    JumpdestCorrect target := by
  unfold bytecodeBridgeChecked? at hCheck
  cases hWindow : targetFitsDecodeWindow? target <;> simp [hWindow] at hCheck
  exact jumpdestCorrect_of_check hCheck

theorem fromBytes_toBytesLE (width value : Nat) :
    EvmYul.fromBytes' (toBytesLE width value) = value % (256 ^ width) := by
  induction width generalizing value with
  | zero =>
      simp [toBytesLE, EvmYul.fromBytes', Nat.mod_one]
  | succ width ih =>
      simp [toBytesLE, EvmYul.fromBytes', ih, UInt8.size]
      have h := Nat.mod_add_div (value % (256 ^ width * 256)) 256
      rw [Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self] at h
      rw [Nat.pow_succ]
      exact h

theorem toBytesLE_length (width value : Nat) :
    (toBytesLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [toBytesLE, ih]

theorem encodeWord32_length (value : Word) :
    (encodeWord32 value).length = 32 := by
  simp [encodeWord32, toBytesLE_length]

theorem encodeInstr_length (instr : TargetInstr) :
    (encodeInstr instr).length = byteSize instr := by
  cases instr with
  | push32 value =>
      simp [encodeInstr, byteSize, encodeWord32_length]
  | jump =>
      rfl
  | jumpi =>
      rfl
  | jumpdest =>
      rfl
  | prim op =>
      rfl

theorem flatMap_encodeLocated_length (code : List LocatedTarget) :
    (code.flatMap encodeLocated).length = codeByteLength code := by
  induction code with
  | nil =>
      rfl
  | cons located rest ih =>
      change
        (encodeLocated located ++ rest.flatMap encodeLocated).length =
          byteSize located.instr + codeByteLength rest
      rw [List.length_append, ih]
      simp [encodeLocated, encodeInstr_length]

theorem encodeTarget_size (target : TargetProgram) :
    (encodeTarget target).size = codeByteLength target.code := by
  cases target with
  | mk code =>
      simpa [encodeTarget, ofList, ByteArray.size, List.size_toArray]
        using flatMap_encodeLocated_length code

theorem encodeTarget_get?_codeByteLength (target : TargetProgram) :
    (encodeTarget target).get? (codeByteLength target.code) = none := by
  unfold ByteArray.get?
  simp [encodeTarget_size]

theorem uint256_ofNat_toNat (value : Word) :
    EvmYul.UInt256.ofNat value.toNat = value := by
  cases value with
  | mk val =>
      unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
      simp
      rfl

theorem uint256_ofNat_toNat_of_lt_size {value : Nat}
    (hValue : value < EvmYul.UInt256.size) :
    (EvmYul.UInt256.ofNat value).toNat = value := by
  unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
  simp
  exact Nat.mod_eq_of_lt hValue

theorem uint256_ofNat_toNat_of_decode_window {value : Nat}
    (hValue : value < 18446744073709551616) :
    (EvmYul.UInt256.ofNat value).toNat = value := by
  apply uint256_ofNat_toNat_of_lt_size
  unfold EvmYul.UInt256.size
  omega

theorem uint256_toNat_lt_256_pow_32 (value : Word) :
    value.toNat < 256 ^ 32 := by
  cases value with
  | mk val =>
      unfold EvmYul.UInt256.toNat
      change ↑val < EvmYul.UInt256.size
      exact val.isLt

theorem extract_push32_payload (value : Word) :
    ((ofList
          (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
            encodeWord32 value)).extract' 1 33).data.toList =
  encodeWord32 value := by
  unfold ByteArray.extract'
  simp [ofList, ByteArray.data_extract, encodeWord32_length]

theorem uint256Of_extract_push32_payload (value : Word) :
    EvmYul.uInt256OfByteArray
        ((ofList
            (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
              encodeWord32 value)).extract' 1 33) =
      value := by
  unfold EvmYul.uInt256OfByteArray
  rw [extract_push32_payload]
  unfold encodeWord32
  simp
  rw [fromBytes_toBytesLE]
  rw [Nat.mod_eq_of_lt (uint256_toNat_lt_256_pow_32 value)]
  exact uint256_ofNat_toNat value

theorem ofList_get?_zero (byte : UInt8) (rest : List UInt8) :
    (ofList (byte :: rest)).get? 0 = some byte := by
  simp [ofList, ByteArray.get?, ByteArray.get, ByteArray.size, List.size_toArray]

theorem ofList_get?_append_cons_append
    (pre payload suffix : List UInt8) (byte : UInt8) :
    (ofList (pre ++ (byte :: payload) ++ suffix)).get? pre.length =
      some byte := by
  simp [ofList, ByteArray.get?, ByteArray.get, ByteArray.size, List.size_toArray]

theorem decode_push32_encode (value : Word) :
    EvmYul.EVM.decode (ofList (encodeInstr (TargetInstr.push32 value)))
        (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.PUSH32, some (value, 32)) := by
  unfold EvmYul.EVM.decode encodeInstr
  change
    (do
      let instr ←
        (ofList
            (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
              encodeWord32 value)).get? 0 >>= EvmYul.EVM.parseInstr
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                      (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                        encodeWord32 value)).extract' 1 (1 + argWidth)),
                argWidth))) =
      some (EvmYul.Operation.PUSH32, some (value, 32))
  rw [ofList_get?_zero]
  change
    (do
      let instr ←
        EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32)
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                      (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                        encodeWord32 value)).extract' 1 (1 + argWidth)),
                argWidth))) =
      some (EvmYul.Operation.PUSH32, some (value, 32))
  have hParse :
      EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32) =
        some EvmYul.Operation.PUSH32 := by
    rfl
  rw [hParse]
  simp [EvmYul.EVM.argOnNBytesOfInstr]
  exact uint256Of_extract_push32_payload value

theorem extract_push32_payload_after_prefix
    (pre suffix : List UInt8) (value : Word)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + 33 < 18446744073709551616) :
    ((ofList
          (pre ++
            (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
              encodeWord32 value) ++
            suffix)).extract' (pre.length + 1) (pre.length + 33)).data.toList =
      encodeWord32 value := by
  unfold ByteArray.extract'
  simp [hStart, hEnd, ofList, ByteArray.data_extract, encodeWord32_length]

theorem uint256Of_extract_push32_payload_after_prefix
    (pre suffix : List UInt8) (value : Word)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + 33 < 18446744073709551616) :
    EvmYul.uInt256OfByteArray
        ((ofList
            (pre ++
              (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                encodeWord32 value) ++
              suffix)).extract' (pre.length + 1) (pre.length + 33)) =
      value := by
  unfold EvmYul.uInt256OfByteArray
  rw [extract_push32_payload_after_prefix pre suffix value hStart hEnd]
  unfold encodeWord32
  simp
  rw [fromBytes_toBytesLE]
  rw [Nat.mod_eq_of_lt (uint256_toNat_lt_256_pow_32 value)]
  exact uint256_ofNat_toNat value

set_option maxHeartbeats 800000 in
theorem decode_push32_at_prefix (pre suffix : List UInt8) (value : Word)
    (hPc : (EvmYul.UInt256.ofNat pre.length).toNat = pre.length)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + 33 < 18446744073709551616) :
    EvmYul.EVM.decode
        (ofList (pre ++ encodeInstr (TargetInstr.push32 value) ++ suffix))
        (EvmYul.UInt256.ofNat pre.length) =
      some (EvmYul.Operation.PUSH32, some (value, 32)) := by
  unfold EvmYul.EVM.decode encodeInstr
  rw [hPc]
  change
    (do
      let instr ←
        (ofList
          (pre ++
            (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
              encodeWord32 value) ++
            suffix)).get? pre.length >>= EvmYul.EVM.parseInstr
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                    (pre ++
                      (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                        encodeWord32 value) ++
                      suffix)).extract' (pre.length + 1)
                    (pre.length + 1 + argWidth)),
                argWidth))) =
      some (EvmYul.Operation.PUSH32, some (value, 32))
  rw [ofList_get?_append_cons_append]
  change
    (do
      let instr ←
        EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32)
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                    (pre ++
                      (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32 ::
                        encodeWord32 value) ++
                      suffix)).extract' (pre.length + 1)
                    (pre.length + 1 + argWidth)),
                argWidth))) =
      some (EvmYul.Operation.PUSH32, some (value, 32))
  have hParse :
      EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32) =
        some EvmYul.Operation.PUSH32 := by
    rfl
  rw [hParse]
  simp [EvmYul.EVM.argOnNBytesOfInstr]
  have hPayload :=
    uint256Of_extract_push32_payload_after_prefix pre suffix value hStart hEnd
  simpa [Nat.add_assoc] using hPayload

theorem decode_single_byte_at_prefix (pre suffix : List UInt8)
    (op : EvmYul.Operation EvmYul.OperationType.EVM)
    (hPc : (EvmYul.UInt256.ofNat pre.length).toNat = pre.length)
    (hParse :
      EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr op) =
        some op)
    (hArgWidth : EvmYul.EVM.argOnNBytesOfInstr op = 0) :
    EvmYul.EVM.decode (ofList (pre ++ [EvmYul.EVM.serializeInstr op] ++ suffix))
        (EvmYul.UInt256.ofNat pre.length) =
      some (op, none) := by
  unfold EvmYul.EVM.decode
  rw [hPc]
  change
    (do
      let instr ←
        (ofList (pre ++ [EvmYul.EVM.serializeInstr op] ++ suffix)).get?
            pre.length >>= EvmYul.EVM.parseInstr
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                      (pre ++ [EvmYul.EVM.serializeInstr op] ++ suffix)).extract'
                    (pre.length + 1) (pre.length + 1 + argWidth)),
                argWidth))) =
      some (op, none)
  rw [ofList_get?_append_cons_append]
  change
    (do
      let instr ← EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr op)
      let argWidth := EvmYul.EVM.argOnNBytesOfInstr instr
      some
        (instr,
          if argWidth == 0 then none
          else
            some
              (EvmYul.uInt256OfByteArray
                  ((ofList
                      (pre ++ [EvmYul.EVM.serializeInstr op] ++ suffix)).extract'
                    (pre.length + 1) (pre.length + 1 + argWidth)),
                argWidth))) =
      some (op, none)
  rw [hParse]
  simp [hArgWidth]

set_option maxHeartbeats 1200000 in
theorem decode_encodeInstr_at_prefix (pre suffix : List UInt8) (instr : TargetInstr)
    (hPc : (EvmYul.UInt256.ofNat pre.length).toNat = pre.length)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + byteSize instr < 18446744073709551616) :
    EvmYul.EVM.decode (ofList (pre ++ encodeInstr instr ++ suffix))
        (EvmYul.UInt256.ofNat pre.length) =
      some (instr.op, instr.arg) := by
  cases instr with
  | push32 value =>
      apply decode_push32_at_prefix
      · exact hPc
      · exact hStart
      · simpa [byteSize] using hEnd
  | jump =>
      exact decode_single_byte_at_prefix pre suffix EvmYul.Operation.JUMP
        hPc rfl rfl
  | jumpi =>
      exact decode_single_byte_at_prefix pre suffix EvmYul.Operation.JUMPI
        hPc rfl rfl
  | jumpdest =>
      exact decode_single_byte_at_prefix pre suffix EvmYul.Operation.JUMPDEST
        hPc rfl rfl
  | prim op =>
      apply decode_single_byte_at_prefix pre suffix op.toEVM hPc
      · cases op <;> rfl
      · cases op <;> rfl

theorem decode_jump_encode :
    EvmYul.EVM.decode (ofList (encodeInstr TargetInstr.jump)) (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.JUMP, none) := by
  rfl

theorem decode_jumpi_encode :
    EvmYul.EVM.decode (ofList (encodeInstr TargetInstr.jumpi)) (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.JUMPI, none) := by
  rfl

theorem decode_jumpdest_encode :
    EvmYul.EVM.decode (ofList (encodeInstr TargetInstr.jumpdest)) (EvmYul.UInt256.ofNat 0) =
      some (EvmYul.Operation.JUMPDEST, none) := by
  rfl

theorem decode_prim_encode (op : PrimOp) :
    EvmYul.EVM.decode (ofList (encodeInstr (TargetInstr.prim op))) (EvmYul.UInt256.ofNat 0) =
      some (op.toEVM, none) := by
  cases op <;> rfl

theorem decode_encodeInstr_zero (instr : TargetInstr) :
    EvmYul.EVM.decode (ofList (encodeInstr instr)) (EvmYul.UInt256.ofNat 0) =
      some (instr.op, instr.arg) := by
  cases instr with
  | push32 value =>
      exact decode_push32_encode value
  | jump =>
      exact decode_jump_encode
  | jumpi =>
      exact decode_jumpi_encode
  | jumpdest =>
      exact decode_jumpdest_encode
  | prim op =>
      exact decode_prim_encode op

theorem fetchInstr_of_decodeAt {bytes : ByteArray} {pc : Nat} {instr : TargetInstr}
    {env : EvmYul.ExecutionEnv EvmYul.OperationType.EVM}
    (hCode : env.code = bytes)
    (hDecode : decodeAt bytes pc instr) :
    EvmYul.EVM.fetchInstr env (EvmYul.UInt256.ofNat pc) =
      .ok (instr.op, instr.arg) := by
  unfold EvmYul.EVM.fetchInstr
  rw [hCode, hDecode]
  rfl

theorem codeLayout_append {first second : List LocatedTarget} {base : Nat}
    (hFirst : codeLayoutFrom first base)
    (hSecond : codeLayoutFrom second (base + codeByteLength first)) :
    codeLayoutFrom (first ++ second) base := by
  induction first generalizing base with
  | nil =>
      simpa [codeLayoutFrom, codeByteLength] using hSecond
  | cons located rest ih =>
      simp [codeLayoutFrom] at hFirst ⊢
      exact ⟨hFirst.1, ih hFirst.2 (by simpa [Nat.add_assoc] using hSecond)⟩

theorem emitInstr_layout {program : Program} {pc : Nat} {instr : Instr}
    {code : List LocatedTarget}
    (hEmit : emitInstr? program pc instr = some code) :
    codeLayoutFrom code pc := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeLayoutFrom]
  | prim op =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeLayoutFrom]
  | push value =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeLayoutFrom]
  | pushLabel target =>
      cases hDest : Program.labelPc program target with
      | none => simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst code
          simp [codeLayoutFrom, byteSize, Instr.push32Size]
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst code
          simp [codeLayoutFrom, byteSize, Instr.push32Size]
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst code
          simp [codeLayoutFrom, byteSize, Instr.push32Size]
  | jumpDynamic =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeLayoutFrom]

theorem emitInstr_byteLength {program : Program} {pc : Nat} {instr : Instr}
    {code : List LocatedTarget}
    (hEmit : emitInstr? program pc instr = some code) :
    codeByteLength code = instr.byteSize := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeByteLength, byteSize, Instr.byteSize]
  | prim op =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeByteLength, byteSize, Instr.byteSize]
  | push value =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeByteLength, byteSize, Instr.byteSize, Instr.push32Size]
  | pushLabel target =>
      cases hDest : Program.labelPc program target with
      | none => simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst code
          simp [codeByteLength, byteSize, Instr.byteSize,
            Instr.push32Size]
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst code
          simp [codeByteLength, byteSize, Instr.byteSize, Instr.jumpSize,
            Instr.push32Size]
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst code
          simp [codeByteLength, byteSize, Instr.byteSize, Instr.jumpSize,
            Instr.push32Size]
  | jumpDynamic =>
      simp [emitInstr?] at hEmit
      subst code
      simp [codeByteLength, byteSize, Instr.byteSize]

theorem emitFrom_layout {program suffix : Program} {base : Nat}
    {code : List LocatedTarget}
    (hEmit : emitFrom? program suffix base = some code) :
    codeLayoutFrom code base := by
  induction suffix generalizing base code with
  | nil =>
      simp [emitFrom?] at hEmit
      subst code
      trivial
  | cons instr rest ih =>
      unfold emitFrom? at hEmit
      cases hHere : emitInstr? program base instr with
      | none =>
          simp [hHere] at hEmit
      | some here =>
          cases hThere : emitFrom? program rest (base + instr.byteSize) with
          | none =>
              simp [hHere, hThere] at hEmit
          | some there =>
              simp [hHere, hThere] at hEmit
              cases hEmit
              have hHereLayout := emitInstr_layout hHere
              have hThereLayout := ih hThere
              have hHereLength := emitInstr_byteLength hHere
              refine codeLayout_append hHereLayout ?_
              simpa [hHereLength] using hThereLayout

theorem emitFrom_byteLength {program suffix : Program} {base : Nat}
    {code : List LocatedTarget}
    (hEmit : emitFrom? program suffix base = some code) :
    codeByteLength code = Program.byteLength suffix := by
  induction suffix generalizing base code with
  | nil =>
      simp [emitFrom?] at hEmit
      subst code
      rfl
  | cons instr rest ih =>
      unfold emitFrom? at hEmit
      cases hHere : emitInstr? program base instr with
      | none =>
          simp [hHere] at hEmit
      | some here =>
          cases hThere : emitFrom? program rest (base + instr.byteSize) with
          | none =>
              simp [hHere, hThere] at hEmit
          | some there =>
              simp [hHere, hThere] at hEmit
              cases hEmit
              have hHereLength := emitInstr_byteLength hHere
              have hThereLength := ih hThere
              simp [codeByteLength_append, Program.byteLength_cons,
                hHereLength, hThereLength]

theorem assemble_layout {program : Program} {target : TargetProgram}
    (hAsm : assemble? program = some target) :
    codeLayoutFrom target.code 0 := by
  unfold assemble? at hAsm
  cases hEmit : emit? program with
  | none =>
      simp [hEmit] at hAsm
  | some code =>
      simp [hEmit] at hAsm
      cases hAsm
      exact emitFrom_layout (program := program) (suffix := program) (base := 0) hEmit

theorem assemble_codeByteLength {program : Program} {target : TargetProgram}
    (hAsm : assemble? program = some target) :
    codeByteLength target.code = Program.byteLength program := by
  unfold assemble? at hAsm
  cases hEmit : emit? program with
  | none =>
      simp [hEmit] at hAsm
  | some code =>
      simp [hEmit] at hAsm
      cases hAsm
      exact
        emitFrom_byteLength (program := program) (suffix := program)
          (base := 0) hEmit

theorem compile_layout {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target) :
    codeLayoutFrom target.code 0 :=
  assemble_layout (Preservation.compile?_some_assemble hCompile)

theorem compile_codeByteLength {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target) :
    codeByteLength target.code = Program.byteLength program :=
  assemble_codeByteLength (Preservation.compile?_some_assemble hCompile)

theorem byteSize_pos (instr : TargetInstr) :
    0 < byteSize instr := by
  cases instr <;> simp [byteSize]

theorem codeLayoutFrom_fetch_end_none
    {code : List LocatedTarget} {base : Nat}
    (hLayout : codeLayoutFrom code base) :
    TargetProgram.fetch { code := code }
        (base + codeByteLength code) = none := by
  induction code generalizing base with
  | nil =>
      simp [TargetProgram.fetch, codeByteLength]
  | cons located rest ih =>
      simp [codeLayoutFrom] at hLayout
      have hNe :
          located.pc ≠
            base + codeByteLength (located :: rest) := by
        rw [hLayout.1]
        have hPos := byteSize_pos located.instr
        simp [codeByteLength]
        omega
      unfold TargetProgram.fetch
      simp only [List.find?_cons]
      simp only [show
        (located.pc == base + codeByteLength (located :: rest)) = false by
          simp [hNe]]
      have hTail :=
        ih (base := base + byteSize located.instr) hLayout.2
      simpa [TargetProgram.fetch, codeByteLength, Nat.add_assoc] using hTail

theorem assemble_fetch_byteLength_none
    {program : Program} {target : TargetProgram}
    (hAsm : assemble? program = some target) :
    target.fetch (Program.byteLength program) = none := by
  have hEnd :=
    codeLayoutFrom_fetch_end_none (assemble_layout hAsm)
  rw [assemble_codeByteLength hAsm] at hEnd
  simpa using hEnd

theorem codeLayoutFrom_member_end_le {code : List LocatedTarget} {base : Nat}
    (hLayout : codeLayoutFrom code base) :
    ∀ located,
      located ∈ code →
        located.pc + byteSize located.instr ≤ base + codeByteLength code := by
  induction code generalizing base with
  | nil =>
      intro located hMem
      simp at hMem
  | cons head rest ih =>
      intro located hMem
      simp [codeLayoutFrom] at hLayout
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst located
          simp [codeByteLength, hLayout.1]
      | inr hRest =>
          have hRestLe :=
            ih (base := base + byteSize head.instr) hLayout.2 located hRest
          simp [codeByteLength]
          omega

theorem decodeSafety_of_layout_and_window {target : TargetProgram}
    (hLayout : codeLayoutFrom target.code 0)
    (hWindow : TargetFitsDecodeWindow target) :
    DecodeSafety target where
  pcNoWrap := by
    intro located hMem
    have hEndLe :=
      codeLayoutFrom_member_end_le (code := target.code) (base := 0)
        hLayout located hMem
    have hPos := byteSize_pos located.instr
    apply uint256_ofNat_toNat_of_decode_window
    unfold TargetFitsDecodeWindow at hWindow
    omega
  extractStartSmall := by
    intro located hMem
    have hEndLe :=
      codeLayoutFrom_member_end_le (code := target.code) (base := 0)
        hLayout located hMem
    have hPos := byteSize_pos located.instr
    unfold TargetFitsDecodeWindow at hWindow
    omega
  extractEndSmall := by
    intro located hMem
    have hEndLe :=
      codeLayoutFrom_member_end_le (code := target.code) (base := 0)
        hLayout located hMem
    unfold TargetFitsDecodeWindow at hWindow
    omega

theorem compile_decodeSafety {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target)
    (hWindow : TargetFitsDecodeWindow target) :
    DecodeSafety target :=
  decodeSafety_of_layout_and_window (compile_layout hCompile) hWindow

set_option maxHeartbeats 1200000 in
theorem codeLayout_decodeAt_with_prefix {code : List LocatedTarget} :
    ∀ {pre suffix : List UInt8} {base : Nat},
      codeLayoutFrom code base →
      pre.length = base →
      (∀ located, located ∈ code →
        (EvmYul.UInt256.ofNat located.pc).toNat = located.pc) →
      (∀ located, located ∈ code →
        located.pc + 1 < 18446744073709551616) →
      (∀ located, located ∈ code →
        located.pc + byteSize located.instr < 18446744073709551616) →
      ∀ located,
        located ∈ code →
          decodeAt (ofList (pre ++ code.flatMap encodeLocated ++ suffix))
            located.pc located.instr := by
  induction code with
  | nil =>
      intro pre suffix base hLayout hPre hPc hStart hEnd located hMem
      simp at hMem
  | cons head rest ih =>
      intro pre suffix base hLayout hPre hPc hStart hEnd located hMem
      simp [codeLayoutFrom] at hLayout
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst located
          have hPrefixHead : pre.length = head.pc := by
            rw [hPre, hLayout.1]
          have hPcHead := hPc head (by simp)
          have hPcPre : (EvmYul.UInt256.ofNat pre.length).toNat = pre.length := by
            simpa [hPrefixHead] using hPcHead
          have hStartHead : pre.length + 1 < 18446744073709551616 := by
            simpa [hPrefixHead] using hStart head (by simp)
          have hEndHead :
              pre.length + byteSize head.instr < 18446744073709551616 := by
            simpa [hPrefixHead] using hEnd head (by simp)
          unfold decodeAt
          rw [← hPrefixHead]
          simpa [encodeLocated, List.append_assoc] using
            decode_encodeInstr_at_prefix pre (rest.flatMap encodeLocated ++ suffix)
              head.instr hPcPre hStartHead hEndHead
      | inr hRest =>
          let pre' := pre ++ encodeInstr head.instr
          have hPre' : pre'.length = base + byteSize head.instr := by
            simp [pre', hPre, encodeInstr_length]
          have hPcRest :
              ∀ located, located ∈ rest →
                (EvmYul.UInt256.ofNat located.pc).toNat = located.pc := by
            intro located hMem
            exact hPc located (by simp [hMem])
          have hStartRest :
              ∀ located, located ∈ rest →
                located.pc + 1 < 18446744073709551616 := by
            intro located hMem
            exact hStart located (by simp [hMem])
          have hEndRest :
              ∀ located, located ∈ rest →
                located.pc + byteSize located.instr < 18446744073709551616 := by
            intro located hMem
            exact hEnd located (by simp [hMem])
          have hDecoded :=
            ih (pre := pre') (suffix := suffix) (base := base + byteSize head.instr)
              hLayout.2 hPre' hPcRest hStartRest hEndRest located hRest
          simpa [pre', encodeLocated, List.append_assoc] using hDecoded

theorem codeLayout_decodes {code : List LocatedTarget}
    (hLayout : codeLayoutFrom code 0)
    (hPc :
      ∀ located, located ∈ code →
        (EvmYul.UInt256.ofNat located.pc).toNat = located.pc)
    (hStart :
      ∀ located, located ∈ code →
        located.pc + 1 < 18446744073709551616)
    (hEnd :
      ∀ located, located ∈ code →
        located.pc + byteSize located.instr < 18446744073709551616) :
    ∀ located,
      located ∈ code →
        decodeAt (ofList (code.flatMap encodeLocated)) located.pc located.instr := by
  intro located hMem
  simpa using
    codeLayout_decodeAt_with_prefix (code := code) (pre := []) (suffix := [])
      (base := 0) hLayout rfl hPc hStart hEnd located hMem

theorem compile_decodingCorrect_with_suffix
    {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target)
    (hSafety : DecodeSafety target)
    (suffix : List UInt8) :
    DecodingCorrect target
      (ofList ((encodeTarget target).toList ++ suffix)) where
  decodes := by
    intro located hMem
    have hDecoded :=
      codeLayout_decodeAt_with_prefix
        (code := target.code) (pre := []) (suffix := suffix) (base := 0)
        (compile_layout hCompile) rfl hSafety.pcNoWrap
        hSafety.extractStartSmall hSafety.extractEndSmall located hMem
    simpa [encodeTarget, ofList] using hDecoded

theorem compile_decode_correct {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target)
    (hSafety : DecodeSafety target) :
    ∀ located,
      located ∈ target.code →
        decodeAt (encodeTarget target) located.pc located.instr := by
  intro located hMem
  unfold encodeTarget
  exact
    codeLayout_decodes (compile_layout hCompile)
      hSafety.pcNoWrap hSafety.extractStartSmall hSafety.extractEndSmall
      located hMem

theorem compile_fetch_correct {program : Program} {target : TargetProgram}
    {env : EvmYul.ExecutionEnv EvmYul.OperationType.EVM}
    (hCompile : compile? program = some target)
    (hSafety : DecodeSafety target)
    (hCode : env.code = encodeTarget target) :
    ∀ located,
      located ∈ target.code →
        EvmYul.EVM.fetchInstr env (EvmYul.UInt256.ofNat located.pc) =
          .ok (located.instr.op, located.instr.arg) := by
  intro located hMem
  exact fetchInstr_of_decodeAt hCode
    (compile_decode_correct hCompile hSafety located hMem)

theorem compile_encoding_correct_of_jumpdests {program : Program}
    {target : TargetProgram}
    (hCompile : compile? program = some target)
    (hSafety : DecodeSafety target)
    (hJumpdest : JumpdestCorrect target) :
    EncodingCorrect target (encodeTarget target) where
  bytes_eq := rfl
  decodes := compile_decode_correct hCompile hSafety
  jumpdests := hJumpdest.jumpdests

/--
Top-level theorem shape for the optional bytecode bridge.

The semantic preservation work is inherited from
`compile_runN_block_trace_projected_sound`; the additional byte-level obligation
is isolated in `EncodingCorrect`, so later work can replace that assumption with
decoder/fetch proofs without changing source-language compilers that target the
assembly AST.
-/
theorem compile_runN_bytecode_bridge {program : Program}
    {target : TargetProgram} {bytes : ByteArray} {fuel : Nat}
    {state sourceState : EVMState}
    (hCompile : compile? program = some target)
    (hBytes : EncodingCorrect target bytes)
    (hRun : Source.runN program fuel state = .ok sourceState) :
    Accepted program ∧
      bytes = encodeTarget target ∧
        ∃ targetState,
          Preservation.BlockTrace program target fuel state targetState ∧
            eraseGas targetState = eraseGas sourceState := by
  obtain ⟨hAccepted, targetState, hTrace, hErase⟩ :=
    Preservation.compile_runN_block_trace_projected_sound hCompile hRun
  exact ⟨hAccepted, hBytes.bytes_eq, targetState, hTrace, hErase⟩

theorem compile_runN_bytecode_bridge_checked {program : Program}
    {target : TargetProgram} {fuel : Nat} {state sourceState : EVMState}
    (hCompile : compile? program = some target)
    (hSafety : DecodeSafety target)
    (hJumpdest : JumpdestCorrect target)
    (hRun : Source.runN program fuel state = .ok sourceState) :
    Accepted program ∧
      ∃ targetState,
        EncodingCorrect target (encodeTarget target) ∧
          Preservation.BlockTrace program target fuel state targetState ∧
            eraseGas targetState = eraseGas sourceState := by
  obtain ⟨hAccepted, targetState, hTrace, hErase⟩ :=
    Preservation.compile_runN_block_trace_projected_sound hCompile hRun
  exact
    ⟨hAccepted, targetState,
      compile_encoding_correct_of_jumpdests hCompile hSafety hJumpdest,
      hTrace, hErase⟩

theorem compile_runN_result_bytecode_bridge_checked {program : Program}
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hSafety : DecodeSafety target)
    (hJumpdest : JumpdestCorrect target)
    (hRun : Source.runNResult program fuel state = .ok result) :
    Accepted program ∧
      EncodingCorrect target (encodeTarget target) ∧
        Preservation.BlockTraceResult program target fuel state result := by
  obtain ⟨hAccepted, hTrace⟩ :=
    Preservation.compile_runN_result_block_trace_sound hCompile hRun
  exact
    ⟨hAccepted,
      compile_encoding_correct_of_jumpdests hCompile hSafety hJumpdest,
      hTrace⟩

end Bytecode

end Assembly
end EvmCompiler
