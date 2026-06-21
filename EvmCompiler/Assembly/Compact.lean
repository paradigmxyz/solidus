import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.InteractionSemantics
import Mathlib.Tactic.IntervalCases

namespace EvmCompiler
namespace Assembly
namespace Compact

/-!
Compact physical layout for resolved Assembly programs.

The ordinary Assembly semantics intentionally uses a uniform 32-byte push
layout. This module leaves that logical semantics unchanged and computes a
separate physical layout. Ordinary constants use their minimum nonzero PUSH
width. Branches use one width chosen from the wide Assembly byte-length upper
bound, so label layout is a single pass rather than a relocation fixed point.
-/

def candidateWidths : List Nat := List.range' 1 32

def FitsWidth (width value : Nat) : Prop :=
  0 < width ∧ width <= 32 ∧ value < 256 ^ width

def fitsWidth? (width value : Nat) : Bool :=
  decide (0 < width) && decide (width <= 32) &&
    decide (value < 256 ^ width)

def widthForNat? (value : Nat) : Option Nat :=
  candidateWidths.find? fun width => fitsWidth? width value

def widthForWord? (value : Word) : Option Nat :=
  widthForNat? value.toNat

theorem widthForNat?_fits {value width : Nat}
    (hWidth : widthForNat? value = some width) :
    FitsWidth width value := by
  unfold widthForNat? at hWidth
  have hMem := List.mem_of_find?_eq_some hWidth
  have hCheck := List.find?_some hWidth
  simp [fitsWidth?] at hCheck
  exact { left := hCheck.1.1, right := { left := hCheck.1.2, right := hCheck.2 } }

def pushOp? : Nat -> Option EVMOp
  | 1 => some EvmYul.Operation.PUSH1
  | 2 => some EvmYul.Operation.PUSH2
  | 3 => some EvmYul.Operation.PUSH3
  | 4 => some EvmYul.Operation.PUSH4
  | 5 => some EvmYul.Operation.PUSH5
  | 6 => some EvmYul.Operation.PUSH6
  | 7 => some EvmYul.Operation.PUSH7
  | 8 => some EvmYul.Operation.PUSH8
  | 9 => some EvmYul.Operation.PUSH9
  | 10 => some EvmYul.Operation.PUSH10
  | 11 => some EvmYul.Operation.PUSH11
  | 12 => some EvmYul.Operation.PUSH12
  | 13 => some EvmYul.Operation.PUSH13
  | 14 => some EvmYul.Operation.PUSH14
  | 15 => some EvmYul.Operation.PUSH15
  | 16 => some EvmYul.Operation.PUSH16
  | 17 => some EvmYul.Operation.PUSH17
  | 18 => some EvmYul.Operation.PUSH18
  | 19 => some EvmYul.Operation.PUSH19
  | 20 => some EvmYul.Operation.PUSH20
  | 21 => some EvmYul.Operation.PUSH21
  | 22 => some EvmYul.Operation.PUSH22
  | 23 => some EvmYul.Operation.PUSH23
  | 24 => some EvmYul.Operation.PUSH24
  | 25 => some EvmYul.Operation.PUSH25
  | 26 => some EvmYul.Operation.PUSH26
  | 27 => some EvmYul.Operation.PUSH27
  | 28 => some EvmYul.Operation.PUSH28
  | 29 => some EvmYul.Operation.PUSH29
  | 30 => some EvmYul.Operation.PUSH30
  | 31 => some EvmYul.Operation.PUSH31
  | 32 => some EvmYul.Operation.PUSH32
  | _ => none

inductive Instr where
  | push (width : Nat) (value : Word)
  | jump
  | jumpi
  | jumpdest
  | prim (op : PrimOp)
  deriving DecidableEq, Repr

namespace Instr

def byteSize : Instr -> Nat
  | .push width _ => width + 1
  | .jump | .jumpi | .jumpdest | .prim _ => 1

def Valid : Instr -> Prop
  | .push width value => FitsWidth width value.toNat
  | .jump | .jumpi | .jumpdest | .prim _ => True

def decoded? : Instr -> Option (Prod EVMOp (Option (Prod Word Nat)))
  | .push width value => do
      let op <- pushOp? width
      some (op, some (value, width))
  | .jump => some (EvmYul.Operation.JUMP, none)
  | .jumpi => some (EvmYul.Operation.JUMPI, none)
  | .jumpdest => some (EvmYul.Operation.JUMPDEST, none)
  | .prim op => some (op.toEVM, none)

def ofTarget? : TargetInstr -> Option Instr
  | .push32 _ => none
  | .jump => some .jump
  | .jumpi => some .jumpi
  | .jumpdest => some .jumpdest
  | .prim op => some (.prim op)

def ofDecoded? (op : EVMOp) (arg : Option (Prod Word Nat)) : Option Instr :=
  match arg with
  | some (value, width) =>
      if pushOp? width = some op then some (.push width value) else none
  | none => (TargetInstr.ofDecoded? op none).bind ofTarget?

theorem ofDecoded?_of_decoded?
    {instr : Instr} {decoded : Prod EVMOp (Option (Prod Word Nat))}
    (hValid : instr.Valid)
    (hDecoded : instr.decoded? = some decoded) :
    ofDecoded? decoded.1 decoded.2 = some instr := by
  cases instr with
  | push width value =>
      cases hOp : pushOp? width with
      | none => simp [decoded?, hOp] at hDecoded
      | some op =>
          simp [decoded?, hOp] at hDecoded
          subst decoded
          simp [ofDecoded?, hOp]
  | jump | jumpi | jumpdest =>
      simp [decoded?, ofDecoded?, ofTarget?] at hDecoded ⊢
      cases hDecoded
      rfl
  | prim op =>
      simp [decoded?] at hDecoded
      cases hDecoded
      unfold ofDecoded?
      have hTarget := TargetInstr.ofDecoded?_op_arg (.prim op)
      change TargetInstr.ofDecoded? op.toEVM none = some (.prim op) at hTarget
      rw [hTarget]
      rfl

theorem byteSize_pos (instr : Instr) : 0 < instr.byteSize := by
  cases instr <;> simp [byteSize]

def valid? : Instr -> Bool
  | .push width value => fitsWidth? width value.toNat
  | .jump | .jumpi | .jumpdest | .prim _ => true

theorem valid_of_check {instr : Instr} (hCheck : instr.valid? = true) :
    instr.Valid := by
  cases instr <;> simp [valid?, Valid, fitsWidth?, FitsWidth] at hCheck ⊢
  exact
    { left := hCheck.1.1
      right := { left := hCheck.1.2, right := hCheck.2 } }

end Instr

structure Located where
  pc : Nat
  instr : Instr
  deriving DecidableEq, Repr

structure Program where
  code : List Located
  deriving DecidableEq, Repr

namespace Program

def codeByteLength : List Located -> Nat
  | [] => 0
  | located :: rest => located.instr.byteSize + codeByteLength rest

def fetch (program : Program) (pc : Nat) : Option Instr :=
  (program.code.find? fun located => located.pc == pc).map Located.instr

def byteLength (program : Program) : Nat :=
  program.code.foldl
    (fun total located => total + located.instr.byteSize) 0

def Valid (program : Program) : Prop :=
  program.code.Forall fun located => located.instr.Valid

def codeLayoutFrom : List Located -> Nat -> Prop
  | [], _ => True
  | located :: rest, pc =>
      located.pc = pc ∧
        codeLayoutFrom rest (pc + located.instr.byteSize)

def layoutFrom? : List Located -> Nat -> Bool
  | [], _ => true
  | located :: rest, pc =>
      decide (located.pc = pc) &&
        layoutFrom? rest (pc + located.instr.byteSize)

def valid? (program : Program) : Bool :=
  program.code.all fun located => located.instr.valid?

def wellFormed? (program : Program) : Bool :=
  program.valid? && layoutFrom? program.code 0 &&
    decide (Program.codeByteLength program.code < 18446744073709551616)

theorem layoutFrom_of_check :
    ∀ {code : List Located} {pc : Nat},
      layoutFrom? code pc = true -> codeLayoutFrom code pc
  | [], _pc, _hCheck => trivial
  | located :: rest, pc, hCheck => by
      simp [layoutFrom?] at hCheck
      exact
        { left := hCheck.1
          right := layoutFrom_of_check hCheck.2 }

theorem valid_of_check {program : Program}
    (hCheck : program.valid? = true) : program.Valid := by
  apply List.forall_iff_forall_mem.mpr
  intro located hMem
  exact Instr.valid_of_check ((List.all_eq_true.mp hCheck) located hMem)

theorem wellFormed_of_check {program : Program}
    (hCheck : program.wellFormed? = true) :
    program.Valid ∧ codeLayoutFrom program.code 0 ∧
      Program.codeByteLength program.code < 18446744073709551616 := by
  simp [wellFormed?] at hCheck
  exact
    { left := valid_of_check hCheck.1.1
      right :=
        { left := layoutFrom_of_check hCheck.1.2
          right := hCheck.2 } }

theorem existsLocatedOfFetch {program : Program}
    {pc : Nat} {instr : Instr}
    (hFetch : program.fetch pc = some instr) :
    ∃ located,
      located ∈ program.code ∧ located.pc = pc ∧ located.instr = instr := by
  unfold fetch at hFetch
  cases hFind : program.code.find? (fun located => located.pc == pc) with
  | none => simp [hFind] at hFetch
  | some located =>
      have hMem : located ∈ program.code :=
        List.mem_of_find?_eq_some hFind
      have hPc : located.pc = pc := by
        have hFound := List.find?_some hFind
        simpa using hFound
      simp [hFind] at hFetch
      subst instr
      exact ⟨located, hMem, hPc, rfl⟩

end Program

abbrev LabelTable := List (Prod Label Nat)

def sourceInstrSize? (branchWidth : Nat) : Assembly.Instr -> Option Nat
  | .label _ | .prim _ => some 1
  | .push value => do
      let width <- widthForWord? value
      some (width + 1)
  | .jump _ | .jumpi _ => some (branchWidth + 2)

def layoutRev? (branchWidth : Nat) :
    Assembly.Program -> Nat -> LabelTable -> Option (Prod LabelTable Nat)
  | [], pc, labels => some (labels.reverse, pc)
  | instr :: rest, pc, labels => do
      let size <- sourceInstrSize? branchWidth instr
      let labels :=
        match instr with
        | .label name => (name, pc) :: labels
        | _ => labels
      layoutRev? branchWidth rest (pc + size) labels

def layout? (source : Assembly.Program) (branchWidth : Nat) :
    Option (Prod LabelTable Nat) :=
  layoutRev? branchWidth source 0 []

def lookupLabel? (table : LabelTable) (target : Label) : Option Nat :=
  (table.find? fun entry => entry.1 == target).map Prod.snd

def emitInstrRev? (branchWidth pc : Nat) (table : LabelTable)
    (instr : Assembly.Instr) (acc : List Located) : Option (List Located) :=
  match instr with
  | .label _ =>
      some ({ pc := pc, instr := .jumpdest } :: acc)
  | .prim op =>
      some ({ pc := pc, instr := .prim op } :: acc)
  | .push value => do
      let width <- widthForWord? value
      some ({ pc := pc, instr := .push width value } :: acc)
  | .jump target => do
      let dest <- lookupLabel? table target
      if fitsWidth? branchWidth dest then
        some
          ({ pc := pc + branchWidth + 1, instr := .jump } ::
            { pc := pc,
              instr := .push branchWidth (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none
  | .jumpi target => do
      let dest <- lookupLabel? table target
      if fitsWidth? branchWidth dest then
        some
          ({ pc := pc + branchWidth + 1, instr := .jumpi } ::
            { pc := pc,
              instr := .push branchWidth (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none

def emitRev? (branchWidth : Nat) (table : LabelTable) :
    Assembly.Program -> Nat -> List Located -> Option (List Located)
  | [], _pc, acc => some acc.reverse
  | instr :: rest, pc, acc => do
      let size <- sourceInstrSize? branchWidth instr
      let acc <- emitInstrRev? branchWidth pc table instr acc
      emitRev? branchWidth table rest (pc + size) acc

def emit? (source : Assembly.Program) (branchWidth : Nat)
    (table : LabelTable) : Option Program := do
  let code <- emitRev? branchWidth table source 0 []
  some { code := code }

def encodePush (width : Nat) (value : Word) : List UInt8 :=
  UInt8.ofNat (0x5f + width) ::
    (Bytecode.toBytesLE width value.toNat).reverse

theorem encodePush_length (width : Nat) (value : Word) :
    (encodePush width value).length = width + 1 := by
  simp [encodePush, Bytecode.toBytesLE_length, Nat.add_comm]

theorem pushOp?_properties {width : Nat} {op : EVMOp}
    (hFits : 0 < width ∧ width <= 32)
    (hOp : pushOp? width = some op) :
    EvmYul.EVM.serializeInstr op = UInt8.ofNat (0x5f + width) ∧
      EvmYul.EVM.argOnNBytesOfInstr op = width := by
  have hPositive : 0 < width := hFits.1
  have hWidth : width <= 32 := hFits.2
  interval_cases width <;> simp [pushOp?] at hOp <;> cases hOp <;> decide

theorem exists_pushOp_of_width {width : Nat}
    (hWidth : 0 < width ∧ width <= 32) :
    ∃ op, pushOp? width = some op := by
  have hPositive : 0 < width := hWidth.1
  have hLe : width <= 32 := hWidth.2
  interval_cases width <;> simp [pushOp?]

theorem extractPushPayloadAfterPrefix
    (pre suffix : List UInt8) (width : Nat) (value : Word)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + width + 1 < 18446744073709551616) :
    ((Bytecode.ofList (pre ++ encodePush width value ++ suffix)).extract'
        (pre.length + 1) (pre.length + width + 1)).data.toList =
      (Bytecode.toBytesLE width value.toNat).reverse := by
  unfold ByteArray.extract'
  simp [hStart, hEnd, Bytecode.ofList, ByteArray.data_extract,
    encodePush, Bytecode.toBytesLE_length]

theorem uint256OfExtractPushPayloadAfterPrefix
    (pre suffix : List UInt8) (width : Nat) (value : Word)
    (hFits : FitsWidth width value.toNat)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + width + 1 < 18446744073709551616) :
    EvmYul.uInt256OfByteArray
        ((Bytecode.ofList (pre ++ encodePush width value ++ suffix)).extract'
          (pre.length + 1) (pre.length + width + 1)) = value := by
  unfold EvmYul.uInt256OfByteArray
  rw [extractPushPayloadAfterPrefix pre suffix width value hStart hEnd]
  simp
  rw [Bytecode.fromBytes_toBytesLE]
  rw [Nat.mod_eq_of_lt hFits.2.2]
  exact Bytecode.uint256_ofNat_toNat value

set_option maxHeartbeats 1200000 in
theorem decodePushAtPrefix
    (pre suffix : List UInt8) (width : Nat) (value : Word) (op : EVMOp)
    (hFits : FitsWidth width value.toNat)
    (hOp : pushOp? width = some op)
    (hPc : (EvmYul.UInt256.ofNat pre.length).toNat = pre.length)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + width + 1 < 18446744073709551616) :
    EvmYul.EVM.decode
        (Bytecode.ofList (pre ++ encodePush width value ++ suffix))
        (EvmYul.UInt256.ofNat pre.length) =
      some (op, some (value, width)) := by
  obtain ⟨hSerialize, hArgWidth⟩ :=
    pushOp?_properties ⟨hFits.1, hFits.2.1⟩ hOp
  unfold EvmYul.EVM.decode
  rw [hPc]
  unfold encodePush
  rw [Bytecode.ofList_get?_append_cons_append]
  rw [← hSerialize]
  have hParse :
      EvmYul.EVM.parseInstr (EvmYul.EVM.serializeInstr op) = some op := by
    have hWidth : width <= 32 := hFits.2.1
    have hPositive : 0 < width := hFits.1
    interval_cases width <;> simp [pushOp?] at hOp <;> cases hOp <;> rfl
  simp [hParse, hArgWidth]
  constructor
  · exact Nat.ne_of_gt hFits.1
  · rw [hSerialize]
    simpa [encodePush, Nat.add_assoc, Nat.add_comm] using
      uint256OfExtractPushPayloadAfterPrefix
        pre suffix width value hFits hStart hEnd

def encodeInstr : Instr -> List UInt8
  | .push width value => encodePush width value
  | .jump => Bytecode.encodeInstr .jump
  | .jumpi => Bytecode.encodeInstr .jumpi
  | .jumpdest => Bytecode.encodeInstr .jumpdest
  | .prim op => Bytecode.encodeInstr (.prim op)

theorem encodeInstr_length (instr : Instr) :
    (encodeInstr instr).length = instr.byteSize := by
  cases instr with
  | push width value =>
      exact encodePush_length width value
  | jump | jumpi | jumpdest => rfl
  | prim op => rfl

def decodeAt (bytes : ByteArray) (pc : Nat) (instr : Instr) : Prop :=
  ∃ decoded,
    instr.decoded? = some decoded ∧
      EvmYul.EVM.decode bytes (EvmYul.UInt256.ofNat pc) = some decoded

theorem decodeInstrAtPrefix
    (pre suffix : List UInt8) (instr : Instr)
    (hValid : instr.Valid)
    (hPc : (EvmYul.UInt256.ofNat pre.length).toNat = pre.length)
    (hStart : pre.length + 1 < 18446744073709551616)
    (hEnd : pre.length + instr.byteSize < 18446744073709551616) :
    decodeAt (Bytecode.ofList (pre ++ encodeInstr instr ++ suffix))
      pre.length instr := by
  cases instr with
  | push width value =>
      obtain ⟨op, hOp⟩ :=
        exists_pushOp_of_width ⟨hValid.1, hValid.2.1⟩
      refine ⟨(op, some (value, width)), ?_, ?_⟩
      · simp [Instr.decoded?, hOp]
      · apply decodePushAtPrefix pre suffix width value op hValid hOp hPc hStart
        simpa [Instr.byteSize, Nat.add_assoc] using hEnd
  | jump =>
      refine ⟨(EvmYul.Operation.JUMP, none), rfl, ?_⟩
      simpa [encodeInstr, Instr.byteSize] using
        Bytecode.decode_encodeInstr_at_prefix pre suffix TargetInstr.jump
          hPc hStart (by simpa [Bytecode.byteSize] using hEnd)
  | jumpi =>
      refine ⟨(EvmYul.Operation.JUMPI, none), rfl, ?_⟩
      simpa [encodeInstr, Instr.byteSize] using
        Bytecode.decode_encodeInstr_at_prefix pre suffix TargetInstr.jumpi
          hPc hStart (by simpa [Bytecode.byteSize] using hEnd)
  | jumpdest =>
      refine ⟨(EvmYul.Operation.JUMPDEST, none), rfl, ?_⟩
      simpa [encodeInstr, Instr.byteSize] using
        Bytecode.decode_encodeInstr_at_prefix pre suffix TargetInstr.jumpdest
          hPc hStart (by simpa [Bytecode.byteSize] using hEnd)
  | prim op =>
      refine ⟨(op.toEVM, none), rfl, ?_⟩
      simpa [encodeInstr, Instr.byteSize] using
        Bytecode.decode_encodeInstr_at_prefix pre suffix (TargetInstr.prim op)
          hPc hStart (by simpa [Bytecode.byteSize] using hEnd)

def encodeLocated (located : Located) : List UInt8 :=
  encodeInstr located.instr

theorem flatMap_encodeLocated_length (code : List Located) :
    (code.flatMap encodeLocated).length = Program.codeByteLength code := by
  induction code with
  | nil => rfl
  | cons located rest ih =>
      simp [encodeLocated, Program.codeByteLength, encodeInstr_length, ih]

def encode (program : Program) : ByteArray :=
  Bytecode.ofList (program.code.flatMap encodeLocated)

structure DecodingCorrect (program : Program) (bytes : ByteArray) : Prop where
  decodes : ∀ located, located ∈ program.code ->
    decodeAt bytes located.pc located.instr

set_option maxHeartbeats 1200000 in
theorem codeLayoutDecodeAtWithPrefix {code : List Located} :
    ∀ {pre suffix : List UInt8} {base : Nat},
      Program.codeLayoutFrom code base ->
      pre.length = base ->
      (∀ located, located ∈ code -> located.instr.Valid) ->
      (∀ located, located ∈ code ->
        (EvmYul.UInt256.ofNat located.pc).toNat = located.pc) ->
      (∀ located, located ∈ code ->
        located.pc + 1 < 18446744073709551616) ->
      (∀ located, located ∈ code ->
        located.pc + located.instr.byteSize < 18446744073709551616) ->
      ∀ located, located ∈ code ->
        decodeAt
          (Bytecode.ofList (pre ++ code.flatMap encodeLocated ++ suffix))
          located.pc located.instr := by
  induction code with
  | nil =>
      intro pre suffix base hLayout hPre hValid hPc hStart hEnd located hMem
      simp at hMem
  | cons head rest ih =>
      intro pre suffix base hLayout hPre hValid hPc hStart hEnd located hMem
      simp [Program.codeLayoutFrom] at hLayout
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst located
          have hPrefixHead : pre.length = head.pc := by
            rw [hPre, hLayout.1]
          have hPcHead := hPc head (by simp)
          have hPcPre :
              (EvmYul.UInt256.ofNat pre.length).toNat = pre.length := by
            simpa [hPrefixHead] using hPcHead
          have hStartHead :
              pre.length + 1 < 18446744073709551616 := by
            simpa [hPrefixHead] using hStart head (by simp)
          have hEndHead :
              pre.length + head.instr.byteSize < 18446744073709551616 := by
            simpa [hPrefixHead] using hEnd head (by simp)
          rw [← hPrefixHead]
          simpa [encodeLocated, List.append_assoc] using
            decodeInstrAtPrefix pre (rest.flatMap encodeLocated ++ suffix)
              head.instr (hValid head (by simp)) hPcPre hStartHead hEndHead
      | inr hRest =>
          let pre' := pre ++ encodeInstr head.instr
          have hPre' : pre'.length = base + head.instr.byteSize := by
            simp [pre', hPre, encodeInstr_length]
          have hValidRest :
              ∀ located, located ∈ rest -> located.instr.Valid := by
            intro located hMem
            exact hValid located (by simp [hMem])
          have hPcRest :
              ∀ located, located ∈ rest ->
                (EvmYul.UInt256.ofNat located.pc).toNat = located.pc := by
            intro located hMem
            exact hPc located (by simp [hMem])
          have hStartRest :
              ∀ located, located ∈ rest ->
                located.pc + 1 < 18446744073709551616 := by
            intro located hMem
            exact hStart located (by simp [hMem])
          have hEndRest :
              ∀ located, located ∈ rest ->
                located.pc + located.instr.byteSize <
                  18446744073709551616 := by
            intro located hMem
            exact hEnd located (by simp [hMem])
          have hDecoded :=
            ih (pre := pre') (suffix := suffix)
              (base := base + head.instr.byteSize)
              hLayout.2 hPre' hValidRest hPcRest hStartRest hEndRest
              located hRest
          simpa [pre', encodeLocated, List.append_assoc] using hDecoded

theorem codeLayoutMemberEndLe {code : List Located} {base : Nat}
    (hLayout : Program.codeLayoutFrom code base) :
    ∀ located, located ∈ code ->
      located.pc + located.instr.byteSize <=
        base + Program.codeByteLength code := by
  induction code generalizing base with
  | nil =>
      intro located hMem
      simp at hMem
  | cons head rest ih =>
      simp [Program.codeLayoutFrom] at hLayout
      intro located hMem
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst located
          simp [Program.codeByteLength, hLayout.1]
      | inr hRest =>
          have hBound := ih hLayout.2 located hRest
          simpa [Program.codeByteLength, Nat.add_assoc] using hBound

theorem decodingCorrectOfWellFormed
    {program : Program}
    (hValid : program.Valid)
    (hLayout : Program.codeLayoutFrom program.code 0)
    (hWindow :
      Program.codeByteLength program.code < 18446744073709551616) :
    DecodingCorrect program (encode program) where
  decodes := by
    intro located hMem
    have hEndLe := codeLayoutMemberEndLe hLayout located hMem
    have hEnd :
        located.pc + located.instr.byteSize <
          18446744073709551616 := by
      omega
    have hStart : located.pc + 1 < 18446744073709551616 := by
      have hSize := Instr.byteSize_pos located.instr
      omega
    have hPcLt : located.pc < 18446744073709551616 := by omega
    have hPc :
        (EvmYul.UInt256.ofNat located.pc).toNat = located.pc :=
      Bytecode.uint256_ofNat_toNat_of_decode_window hPcLt
    have hDecoded :=
      codeLayoutDecodeAtWithPrefix
        (code := program.code) (pre := []) (suffix := []) (base := 0)
        hLayout rfl
        (fun item hItem =>
          (List.forall_iff_forall_mem.mp hValid) item hItem)
        (fun item hItem => by
          have hItemEnd := codeLayoutMemberEndLe hLayout item hItem
          have hItemPc : item.pc < 18446744073709551616 := by
            have hItemSize := Instr.byteSize_pos item.instr
            omega
          exact Bytecode.uint256_ofNat_toNat_of_decode_window hItemPc)
        (fun item hItem => by
          have hItemEnd := codeLayoutMemberEndLe hLayout item hItem
          have hItemSize := Instr.byteSize_pos item.instr
          omega)
        (fun item hItem => by
          have hItemEnd := codeLayoutMemberEndLe hLayout item hItem
          omega)
        located hMem
    simpa [encode, Bytecode.ofList] using hDecoded

/-- Remove an unconditional transfer to the label physically adjacent to it.
The label remains available to every other incoming edge. -/
def elideFallthroughJumps : Assembly.Program -> Assembly.Program
  | .jump target :: .label next :: rest =>
      if target = next then
        .label next :: elideFallthroughJumps rest
      else
        .jump target :: elideFallthroughJumps (.label next :: rest)
  | instr :: rest => instr :: elideFallthroughJumps rest
  | [] => []
termination_by source => source.length
decreasing_by all_goals (simp_wf <;> omega)

def referencedLabels (source : Assembly.Program) : List Label :=
  source.flatMap Assembly.Instr.targets

def pruneUnreferencedLabels (targets : List Label) :
    Assembly.Program -> Assembly.Program
  | [] => []
  | .label name :: rest =>
      if name ∈ targets then
        .label name :: pruneUnreferencedLabels targets rest
      else
        pruneUnreferencedLabels targets rest
  | instr :: rest => instr :: pruneUnreferencedLabels targets rest

def prepare (source : Assembly.Program) : Assembly.Program :=
  let elided := elideFallthroughJumps source
  pruneUnreferencedLabels (referencedLabels elided) elided

structure Artifact where
  physicalSource : Assembly.Program
  branchWidth : Nat
  labels : LabelTable
  codeLength : Nat
  program : Program
  bytes : ByteArray
  deriving Repr

structure SourceStats where
  instructions : Nat := 0
  labels : Nat := 0
  pushes : Nat := 0
  zeroPushes : Nat := 0
  jumps : Nat := 0
  jumpis : Nat := 0
  adds : Nat := 0
  pops : Nat := 0
  dups : Nat := 0
  swaps : Nat := 0
  otherPrims : Nat := 0
  deriving Repr

def SourceStats.addInstr (stats : SourceStats)
    (instr : Assembly.Instr) : SourceStats :=
  match instr with
  | .label _ =>
      { stats with
        instructions := stats.instructions + 1
        labels := stats.labels + 1 }
  | .push value =>
      { stats with
        instructions := stats.instructions + 1
        pushes := stats.pushes + 1
        zeroPushes := stats.zeroPushes + if value.toNat = 0 then 1 else 0 }
  | .jump _ =>
      { stats with
        instructions := stats.instructions + 1
        jumps := stats.jumps + 1 }
  | .jumpi _ =>
      { stats with
        instructions := stats.instructions + 1
        jumpis := stats.jumpis + 1 }
  | .prim op =>
      let opcode := (EvmYul.EVM.serializeInstr op.toEVM).toNat
      let isDup := decide (0x80 <= opcode ∧ opcode <= 0x8f)
      let isSwap := decide (0x90 <= opcode ∧ opcode <= 0x9f)
      { stats with
        instructions := stats.instructions + 1
        adds := stats.adds + if op = .add then 1 else 0
        pops := stats.pops + if op = .pop then 1 else 0
        dups := stats.dups + if isDup then 1 else 0
        swaps := stats.swaps + if isSwap then 1 else 0
        otherPrims := stats.otherPrims +
          if op != .add && op != .pop &&
              !isDup && !isSwap then 1 else 0 }

def sourceStats (source : Assembly.Program) : SourceStats :=
  source.foldl SourceStats.addInstr {}

def compile? (source : Assembly.Program) : Option Artifact := do
  let physicalSource := prepare source
  let branchWidth <- widthForNat? physicalSource.byteLength
  let (labels, codeLength) <- layout? physicalSource branchWidth
  let program <- emit? physicalSource branchWidth labels
  if program.wellFormed? then
    some
      { physicalSource := physicalSource
        branchWidth := branchWidth
        labels := labels
        codeLength := codeLength
        program := program
        bytes := encode program }
  else
    none

structure Artifact.ValidFor (artifact : Artifact)
    (source : Assembly.Program) : Prop where
  physicalSource : artifact.physicalSource = prepare source
  branchWidth : widthForNat? artifact.physicalSource.byteLength =
    some artifact.branchWidth
  layout : layout? artifact.physicalSource artifact.branchWidth =
    some (artifact.labels, artifact.codeLength)
  emitted : emit? artifact.physicalSource artifact.branchWidth artifact.labels =
    some artifact.program
  wellFormed : artifact.program.Valid ∧
    Program.codeLayoutFrom artifact.program.code 0 ∧
      Program.codeByteLength artifact.program.code < 18446744073709551616
  bytes : artifact.bytes = encode artifact.program

theorem compile?_valid {source : Assembly.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    artifact.ValidFor source := by
  unfold compile? at hCompile
  generalize hPhysical : prepare source = physicalSource at hCompile
  cases hWidth : widthForNat? physicalSource.byteLength with
  | none => simp [hWidth] at hCompile
  | some branchWidth =>
      simp [hWidth] at hCompile
      cases hLayout : layout? physicalSource branchWidth with
      | none => simp [hLayout] at hCompile
      | some layoutResult =>
          cases layoutResult with
          | mk labels codeLength =>
              simp [hLayout] at hCompile
              cases hEmit : emit? physicalSource branchWidth labels with
              | none => simp [hEmit] at hCompile
              | some program =>
                  simp [hEmit] at hCompile
                  by_cases hWellFormed : program.wellFormed? = true
                  · simp [hWellFormed] at hCompile
                    cases hCompile
                    exact
                      Artifact.ValidFor.mk hPhysical.symm hWidth hLayout hEmit
                        (Program.wellFormed_of_check hWellFormed) rfl
                  · simp [hWellFormed] at hCompile

theorem compile?_decodingCorrect
    {source : Assembly.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    DecodingCorrect artifact.program artifact.bytes := by
  have hValid := compile?_valid hCompile
  rw [hValid.bytes]
  exact
    decodingCorrectOfWellFormed
      hValid.wellFormed.1 hValid.wellFormed.2.1 hValid.wellFormed.2.2

namespace Instr

def openStepResult : Instr -> EVMState ->
    Assembly.InteractionSemantics.OpenStepResult
  | .push width value, state =>
      Assembly.InteractionSemantics.Target.openStepPushResult
        width value state
  | .jump, state =>
      Assembly.InteractionSemantics.Target.openStepInstrResult .jump state
  | .jumpi, state =>
      Assembly.InteractionSemantics.Target.openStepInstrResult .jumpi state
  | .jumpdest, state =>
      Assembly.InteractionSemantics.Target.openStepInstrResult .jumpdest state
  | .prim op, state =>
      Assembly.InteractionSemantics.Target.openStepInstrResult (.prim op) state

end Instr

namespace InteractionSemantics

/-- Actual compact-byte execution. Decoding is imported from EVMYulLean and
instruction effects reuse the Assembly target kernels. -/
def openStepResult (bytes : ByteArray) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match EvmYul.EVM.decode bytes state.pc with
  | none => .done (.error .InvalidInstruction)
  | some (op, arg) =>
      match Instr.ofDecoded? op arg with
      | none => .done (.error .InvalidInstruction)
      | some instr => instr.openStepResult state

def openRunNResult (bytes : ByteArray) (fuel : Nat) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  Assembly.Control.runNResultWith (openStepResult bytes) fuel state

end InteractionSemantics

theorem openStepResultEqInstrOfDecodeAt
    {bytes : ByteArray} {pc : Nat} {instr : Instr} {state : EVMState}
    (hValid : instr.Valid)
    (hDecode : decodeAt bytes pc instr)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    InteractionSemantics.openStepResult bytes state =
      instr.openStepResult state := by
  rcases hDecode with ⟨decoded, hInstr, hBytes⟩
  unfold InteractionSemantics.openStepResult
  rw [hPc, hBytes]
  simp [Instr.ofDecoded?_of_decoded? hValid hInstr]

end Compact
end Assembly
end EvmCompiler
