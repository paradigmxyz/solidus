import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.InteractionPreservation
import Mathlib.Tactic.IntervalCases
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

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

def PCIndependent : Instr -> Prop
  | .prim .pc => False
  | _ => True

def Sequential : Instr -> Prop
  | .jump | .jumpi => False
  | _ => True

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

def pcIndependent? : Instr -> Bool
  | .prim .pc => false
  | _ => true

theorem valid_of_check {instr : Instr} (hCheck : instr.valid? = true) :
    instr.Valid := by
  cases instr <;> simp [valid?, Valid, fitsWidth?, FitsWidth] at hCheck ⊢
  exact
    { left := hCheck.1.1
      right := { left := hCheck.1.2, right := hCheck.2 } }

theorem pcIndependent_of_check {instr : Instr}
    (hCheck : instr.pcIndependent? = true) : instr.PCIndependent := by
  cases instr <;> simp [pcIndependent?, PCIndependent] at hCheck ⊢
  rename_i op
  cases op <;> simp [PCIndependent] at hCheck ⊢

end Instr

structure Located where
  pc : Nat
  instr : Instr
  deriving DecidableEq, Repr

structure Program where
  code : List Located
  deriving DecidableEq, Repr

namespace Program

def codeByteLengthFast (code : List Located) : Nat :=
  code.foldl (fun total located => total + located.instr.byteSize) 0

@[implemented_by codeByteLengthFast]
def codeByteLength : List Located -> Nat
  | [] => 0
  | located :: rest => located.instr.byteSize + codeByteLength rest

private theorem foldl_byteSize_eq (code : List Located) (total : Nat) :
    code.foldl (fun acc located => acc + located.instr.byteSize) total =
      total + codeByteLength code := by
  induction code generalizing total with
  | nil => simp [codeByteLength]
  | cons located rest ih =>
      simp only [List.foldl_cons, codeByteLength]
      rw [ih]
      omega

theorem codeByteLengthFast_eq (code : List Located) :
    codeByteLengthFast code = codeByteLength code := by
  simp [codeByteLengthFast, foldl_byteSize_eq]

theorem codeByteLength_append (left right : List Located) :
    codeByteLength (left ++ right) =
      codeByteLength left + codeByteLength right := by
  induction left with
  | nil => simp [codeByteLength]
  | cons located rest ih =>
      simp [codeByteLength, ih, Nat.add_assoc]

def fetch (program : Program) (pc : Nat) : Option Instr :=
  (program.code.find? fun located => located.pc == pc).map Located.instr

def byteLength (program : Program) : Nat :=
  program.code.foldl
    (fun total located => total + located.instr.byteSize) 0

def Valid (program : Program) : Prop :=
  program.code.Forall fun located => located.instr.Valid

def PCIndependent (program : Program) : Prop :=
  program.code.Forall fun located => located.instr.PCIndependent

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

def layoutFromFast? : List Located → Nat → Bool
  | [], _ => true
  | located :: rest, pc =>
      if located.pc == pc then
        layoutFromFast? rest (pc + located.instr.byteSize)
      else
        false

theorem layoutFromFast?_eq (code : List Located) (pc : Nat) :
    layoutFromFast? code pc = layoutFrom? code pc := by
  induction code generalizing pc with
  | nil => rfl
  | cons located rest ih =>
      by_cases hPc : located.pc = pc
      · simp [layoutFromFast?, layoutFrom?, hPc, ih]
      · simp [layoutFromFast?, layoutFrom?, hPc]

def valid? (program : Program) : Bool :=
  program.code.all fun located => located.instr.valid?

def pcIndependent? (program : Program) : Bool :=
  program.code.all fun located => located.instr.pcIndependent?

def wellFormedFast? (program : Program) : Bool :=
  program.valid? && layoutFromFast? program.code 0 &&
    decide (Program.codeByteLengthFast program.code < 18446744073709551616) &&
      program.pcIndependent?

@[implemented_by wellFormedFast?]
def wellFormed? (program : Program) : Bool :=
  program.valid? && layoutFrom? program.code 0 &&
    decide (Program.codeByteLength program.code < 18446744073709551616) &&
      program.pcIndependent?

theorem wellFormedFast?_eq (program : Program) :
    wellFormedFast? program = wellFormed? program := by
  simp [wellFormedFast?, wellFormed?, layoutFromFast?_eq,
    codeByteLengthFast_eq]

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

theorem pcIndependent_of_check {program : Program}
    (hCheck : program.pcIndependent? = true) : program.PCIndependent := by
  apply List.forall_iff_forall_mem.mpr
  intro located hMem
  exact Instr.pcIndependent_of_check
    ((List.all_eq_true.mp hCheck) located hMem)

theorem wellFormed_of_check {program : Program}
    (hCheck : program.wellFormed? = true) :
    program.Valid ∧ codeLayoutFrom program.code 0 ∧
      Program.codeByteLength program.code < 18446744073709551616 ∧
        program.PCIndependent := by
  simp [wellFormed?] at hCheck
  exact
    { left := valid_of_check hCheck.1.1.1
      right :=
        { left := layoutFrom_of_check hCheck.1.1.2
          right :=
            { left := hCheck.1.2
              right := pcIndependent_of_check hCheck.2 } } }

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

def pushWidthAt? (pinnedPushPcs : List Nat) (sourcePc : Nat)
    (value : Word) : Option Nat :=
  if pinnedPushPcs.contains sourcePc then some 32 else widthForWord? value

def sourceInstrSizeAt? (pinnedPushPcs : List Nat) (branchWidth sourcePc : Nat) :
    Assembly.Instr -> Option Nat
  | .label _ | .prim _ => some 1
  | .push value => do
      let width <- pushWidthAt? pinnedPushPcs sourcePc value
      some (width + 1)
  | .jump _ | .jumpi _ => some (branchWidth + 2)
  | .pushLabel _ | .jumpDynamic => none

def layoutRev? (pinnedPushPcs : List Nat) (branchWidth : Nat) :
    Assembly.Program -> Nat -> Nat -> LabelTable -> Option (Prod LabelTable Nat)
  | [], _sourcePc, compactPc, labels => some (labels.reverse, compactPc)
  | instr :: rest, sourcePc, compactPc, labels => do
      let size <- sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr
      let labels :=
        match instr with
        | .label name => (name, compactPc) :: labels
        | _ => labels
      layoutRev? pinnedPushPcs branchWidth rest
        (sourcePc + instr.byteSize) (compactPc + size) labels

def layout? (pinnedPushPcs : List Nat) (source : Assembly.Program)
    (branchWidth : Nat) :
    Option (Prod LabelTable Nat) :=
  layoutRev? pinnedPushPcs branchWidth source 0 0 []

/-- A branch width is viable when the complete compact layout fits strictly
below the largest destination representable at that width. -/
def branchWidthFits? (pinnedPushPcs : List Nat)
    (source : Assembly.Program) (branchWidth : Nat) : Bool :=
  match layout? pinnedPushPcs source branchWidth with
  | none => false
  | some (_, codeLength) => fitsWidth? branchWidth codeLength

def branchWidthFor? (pinnedPushPcs : List Nat)
    (source : Assembly.Program) : Option Nat :=
  candidateWidths.find? fun width =>
    branchWidthFits? pinnedPushPcs source width

def lookupLabel? (table : LabelTable) (target : Label) : Option Nat :=
  (table.find? fun entry => entry.1 == target).map Prod.snd

theorem layoutRev?_names
    {pinnedPushPcs : List Nat} {branchWidth sourcePc compactPc endPc : Nat}
    {source : Assembly.Program}
    {acc table : LabelTable}
    (hLayout : layoutRev? pinnedPushPcs branchWidth source
      sourcePc compactPc acc =
      some (table, endPc)) :
    table.map Prod.fst = acc.reverse.map Prod.fst ++ source.labels := by
  induction source generalizing sourcePc compactPc acc table endPc with
  | nil =>
      simp [layoutRev?] at hLayout
      rcases hLayout with ⟨rfl, rfl⟩
      simp [Assembly.Program.labels]
  | cons instr rest ih =>
      cases hSize :
          sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr with
      | none => simp [layoutRev?, hSize] at hLayout
      | some size =>
          cases instr with
          | label name =>
              have hTail : layoutRev? pinnedPushPcs branchWidth rest
                  (sourcePc + (Assembly.Instr.label name).byteSize)
                  (compactPc + size)
                  ((name, compactPc) :: acc) = some (table, endPc) := by
                simpa [layoutRev?, hSize] using hLayout
              have hRest := ih hTail
              simpa [Assembly.Program.labels, List.reverse_cons,
                List.map_append, List.append_assoc] using hRest
          | prim op | push op | pushLabel op | jump op | jumpi op =>
              have hTail := hLayout
              simp [layoutRev?, hSize] at hTail
              have hRest := ih hTail
              simpa [Assembly.Program.labels] using hRest
          | jumpDynamic =>
              have hTail := hLayout
              simp [layoutRev?, hSize] at hTail
              have hRest := ih hTail
              simpa [Assembly.Program.labels] using hRest

theorem lookupLabel?_name_mem
    {table : LabelTable} {target : Label} {pc : Nat}
    (hLookup : lookupLabel? table target = some pc) :
    target ∈ table.map Prod.fst := by
  unfold lookupLabel? at hLookup
  cases hFind : table.find? (fun entry => entry.1 == target) with
  | none => simp [hFind] at hLookup
  | some entry =>
      have hMem : entry ∈ table := List.mem_of_find?_eq_some hFind
      have hName : entry.1 = target := by
        have hFound := List.find?_some hFind
        simpa using hFound
      apply List.mem_map.mpr
      exact ⟨entry, hMem, hName⟩

def emitInstrRev? (pinnedPushPcs : List Nat)
    (branchWidth sourcePc compactPc : Nat) (table : LabelTable)
    (instr : Assembly.Instr) (acc : List Located) : Option (List Located) :=
  match instr with
  | .label _ =>
      some ({ pc := compactPc, instr := .jumpdest } :: acc)
  | .prim op =>
      some ({ pc := compactPc, instr := .prim op } :: acc)
  | .push value => do
      let width <- pushWidthAt? pinnedPushPcs sourcePc value
      some ({ pc := compactPc, instr := .push width value } :: acc)
  | .pushLabel _ => none
  | .jump target => do
      let dest <- lookupLabel? table target
      if fitsWidth? branchWidth dest then
        some
          ({ pc := compactPc + branchWidth + 1, instr := .jump } ::
            { pc := compactPc,
              instr := .push branchWidth (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none
  | .jumpi target => do
      let dest <- lookupLabel? table target
      if fitsWidth? branchWidth dest then
        some
          ({ pc := compactPc + branchWidth + 1, instr := .jumpi } ::
            { pc := compactPc,
              instr := .push branchWidth (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none
  | .jumpDynamic => none

def emitRev? (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (table : LabelTable) :
    Assembly.Program -> Nat -> Nat -> List Located -> Option (List Located)
  | [], _sourcePc, _compactPc, acc => some acc.reverse
  | instr :: rest, sourcePc, compactPc, acc => do
      let size <- sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr
      let acc <- emitInstrRev? pinnedPushPcs branchWidth sourcePc compactPc
        table instr acc
      emitRev? pinnedPushPcs branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + size) acc

def emit? (pinnedPushPcs : List Nat) (source : Assembly.Program) (branchWidth : Nat)
    (table : LabelTable) : Option Program := do
  let code <- emitRev? pinnedPushPcs branchWidth table source 0 0 []
  some { code := code }

structure SourceBlock where
  sourcePc : Nat
  compactPc : Nat
  sourceInstr : Assembly.Instr
  code : List Located
  deriving DecidableEq, Repr

def emitSourceBlock? (pinnedPushPcs : List Nat)
    (branchWidth sourcePc compactPc : Nat) (table : LabelTable)
    (instr : Assembly.Instr) : Option (List Located) := do
  let reversed <- emitInstrRev? pinnedPushPcs branchWidth sourcePc compactPc
    table instr []
  some reversed.reverse

def emitBlocksFromRev? (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (table : LabelTable) :
    Assembly.Program → Nat → Nat → List SourceBlock →
      Option (List SourceBlock)
  | [], _sourcePc, _compactPc, acc => some acc.reverse
  | instr :: rest, sourcePc, compactPc, acc => do
      let compactSize ←
        sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr
      let code ←
        emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc
          table instr
      emitBlocksFromRev? pinnedPushPcs branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + compactSize)
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: acc)

def emitBlocksFromFast? (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (table : LabelTable) (source : Assembly.Program)
    (sourcePc compactPc : Nat) : Option (List SourceBlock) :=
  emitBlocksFromRev? pinnedPushPcs branchWidth table source
    sourcePc compactPc []

@[implemented_by emitBlocksFromFast?]
def emitBlocksFrom? (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (table : LabelTable) :
    Assembly.Program -> Nat -> Nat -> Option (List SourceBlock)
  | [], _sourcePc, _compactPc => some []
  | instr :: rest, sourcePc, compactPc => do
      let compactSize <-
        sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr
      let code <- emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc
        table instr
      let blocks <-
        emitBlocksFrom? pinnedPushPcs branchWidth table rest
          (sourcePc + instr.byteSize) (compactPc + compactSize)
      some
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: blocks)

def emitBlocksFast? (pinnedPushPcs : List Nat) (source : Assembly.Program)
    (branchWidth : Nat) (table : LabelTable) : Option (List SourceBlock) :=
  emitBlocksFromFast? pinnedPushPcs branchWidth table source 0 0

@[implemented_by emitBlocksFast?]
def emitBlocks? (pinnedPushPcs : List Nat) (source : Assembly.Program)
    (branchWidth : Nat)
    (table : LabelTable) : Option (List SourceBlock) :=
  emitBlocksFrom? pinnedPushPcs branchWidth table source 0 0

private theorem emitBlocksFromRev_eq
    (pinnedPushPcs : List Nat) (branchWidth : Nat) (table : LabelTable) :
    ∀ (source : Assembly.Program) (sourcePc compactPc : Nat)
      (acc : List SourceBlock),
      emitBlocksFromRev? pinnedPushPcs branchWidth table source
          sourcePc compactPc acc = do
        let blocks ←
          emitBlocksFrom? pinnedPushPcs branchWidth table source
            sourcePc compactPc
        some (acc.reverse ++ blocks)
  | [], sourcePc, compactPc, acc => by
      simp [emitBlocksFromRev?, emitBlocksFrom?]
  | instr :: rest, sourcePc, compactPc, acc => by
      cases hSize :
          sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr with
      | none =>
          simp [emitBlocksFromRev?, emitBlocksFrom?, hSize]
      | some compactSize =>
          cases hCode :
              emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc
                table instr with
          | none =>
              simp [emitBlocksFromRev?, emitBlocksFrom?, hSize, hCode]
          | some code =>
              simp [emitBlocksFromRev?, emitBlocksFrom?, hSize, hCode,
                emitBlocksFromRev_eq, List.reverse_cons,
                List.append_assoc]
              cases hTail :
                  emitBlocksFrom? pinnedPushPcs branchWidth table rest
                    (sourcePc + instr.byteSize)
                    (compactPc + compactSize) <;> simp [hTail]

theorem emitBlocksFromFast_eq
    (pinnedPushPcs : List Nat) (branchWidth : Nat) (table : LabelTable)
    (source : Assembly.Program) (sourcePc compactPc : Nat) :
    emitBlocksFromFast? pinnedPushPcs branchWidth table source
        sourcePc compactPc =
      emitBlocksFrom? pinnedPushPcs branchWidth table source
        sourcePc compactPc := by
  simp [emitBlocksFromFast?, emitBlocksFromRev_eq]

theorem emitBlocksFast_eq
    (pinnedPushPcs : List Nat) (source : Assembly.Program)
    (branchWidth : Nat) (table : LabelTable) :
    emitBlocksFast? pinnedPushPcs source branchWidth table =
      emitBlocks? pinnedPushPcs source branchWidth table := by
  simp [emitBlocksFast?, emitBlocks?, emitBlocksFromFast_eq]

def blocksCodeRev : List SourceBlock → List Located → List Located
  | [], acc => acc.reverse
  | block :: rest, acc =>
      blocksCodeRev rest (block.code.reverse ++ acc)

def blocksCodeFast (blocks : List SourceBlock) : List Located :=
  blocksCodeRev blocks []

@[implemented_by blocksCodeFast]
def blocksCode (blocks : List SourceBlock) : List Located :=
  blocks.flatMap SourceBlock.code

private theorem blocksCodeRev_eq (blocks : List SourceBlock)
    (acc : List Located) :
    blocksCodeRev blocks acc = acc.reverse ++ blocksCode blocks := by
  induction blocks generalizing acc with
  | nil => simp [blocksCodeRev, blocksCode]
  | cons block rest ih =>
      simp [blocksCodeRev, blocksCode, ih, List.reverse_append,
        List.append_assoc]

theorem blocksCodeFast_eq (blocks : List SourceBlock) :
    blocksCodeFast blocks = blocksCode blocks := by
  simp [blocksCodeFast, blocksCodeRev_eq]

def locatedListEq? : List Located → List Located → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      if left == right then locatedListEq? leftRest rightRest else false
  | _, _ => false

theorem locatedListEq?_eq_true_iff (left right : List Located) :
    locatedListEq? left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [locatedListEq?]
  | cons head tail ih =>
      cases right with
      | nil => simp [locatedListEq?]
      | cons other rest =>
          simp [locatedListEq?, ih]

def blocksCodeMatches? (blocks : List SourceBlock)
    (code : List Located) : Bool :=
  locatedListEq? (blocksCodeFast blocks) code

theorem blocksCodeMatches?_eq_true_iff
    (blocks : List SourceBlock) (code : List Located) :
    blocksCodeMatches? blocks code = true ↔ blocksCode blocks = code := by
  simp [blocksCodeMatches?, locatedListEq?_eq_true_iff, blocksCodeFast_eq]

theorem blocksCodeMatches_of_check
    {blocks : List SourceBlock} {code : List Located}
    (hCheck : blocksCodeMatches? blocks code = true) :
    blocksCode blocks = code :=
  (blocksCodeMatches?_eq_true_iff blocks code).mp hCheck

def blockLabelConsistent? (table : LabelTable) (block : SourceBlock) : Bool :=
  match block.sourceInstr with
  | .label name => lookupLabel? table name == some block.compactPc
  | _ => true

def labelsConsistent? (blocks : List SourceBlock) (table : LabelTable) : Bool :=
  blocks.all (blockLabelConsistent? table)

def LabelsConsistent (blocks : List SourceBlock) (table : LabelTable) : Prop :=
  ∀ block, block ∈ blocks -> ∀ name,
    block.sourceInstr = .label name ->
      lookupLabel? table name = some block.compactPc

theorem labelsConsistent_of_check
    {blocks : List SourceBlock} {table : LabelTable}
    (hCheck : labelsConsistent? blocks table = true) :
    LabelsConsistent blocks table := by
  intro block hMem name hInstr
  have hBlock := (List.all_eq_true.mp hCheck) block hMem
  unfold blockLabelConsistent? at hBlock
  rw [hInstr] at hBlock
  simpa using hBlock

inductive BlocksValidFrom (pinnedPushPcs : List Nat)
    (branchWidth : Nat) (table : LabelTable) :
    Assembly.Program -> Nat -> Nat -> List SourceBlock -> Prop
  | nil (sourcePc compactPc : Nat) :
      BlocksValidFrom pinnedPushPcs branchWidth table [] sourcePc compactPc []
  | cons (instr : Assembly.Instr) (rest : Assembly.Program)
      (sourcePc compactPc compactSize : Nat)
      (code : List Located) (blocks : List SourceBlock)
      (hSize : sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr =
        some compactSize)
      (hCode :
        emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc table
          instr = some code)
      (hRest : BlocksValidFrom pinnedPushPcs branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + compactSize) blocks) :
      BlocksValidFrom pinnedPushPcs branchWidth table (instr :: rest)
        sourcePc compactPc
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: blocks)

theorem emitBlocksFrom?_valid
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable} :
    forall {source : Assembly.Program} {sourcePc compactPc : Nat}
      {blocks : List SourceBlock},
      emitBlocksFrom? pinnedPushPcs branchWidth table source sourcePc compactPc =
          some blocks ->
        BlocksValidFrom pinnedPushPcs branchWidth table source sourcePc
          compactPc blocks := by
  intro source
  induction source with
  | nil =>
      intro sourcePc compactPc blocks hEmit
      simp [emitBlocksFrom?] at hEmit
      subst blocks
      exact .nil sourcePc compactPc
  | cons instr rest ih =>
      intro sourcePc compactPc blocks hEmit
      unfold emitBlocksFrom? at hEmit
      cases hSize :
          sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr with
      | none => simp [hSize] at hEmit
      | some compactSize =>
          simp [hSize] at hEmit
          cases hCode :
              emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc
                table instr with
          | none => simp [hCode] at hEmit
          | some code =>
              simp [hCode] at hEmit
              cases hRest :
                  emitBlocksFrom? pinnedPushPcs branchWidth table rest
                    (sourcePc + instr.byteSize)
                    (compactPc + compactSize) with
              | none => simp [hRest] at hEmit
              | some restBlocks =>
                  simp [hRest] at hEmit
                  subst blocks
                  exact .cons instr rest sourcePc compactPc compactSize
                    code restBlocks hSize hCode (ih hRest)

theorem emitBlocks?_valid
    {pinnedPushPcs : List Nat} {source : Assembly.Program}
    {branchWidth : Nat} {table : LabelTable}
    {blocks : List SourceBlock}
    (hEmit : emitBlocks? pinnedPushPcs source branchWidth table = some blocks) :
    BlocksValidFrom pinnedPushPcs branchWidth table source 0 0 blocks := by
  exact emitBlocksFrom?_valid hEmit

theorem emitSourceBlock?_codeByteLength
    {pinnedPushPcs : List Nat}
    {branchWidth sourcePc compactPc compactSize : Nat} {table : LabelTable}
    {instr : Assembly.Instr} {code : List Located}
    (hSize : sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr =
      some compactSize)
    (hCode : emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc
      table instr = some code) :
    Program.codeByteLength code = compactSize := by
  cases instr with
  | label name | prim name =>
      simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?]
        at hSize hCode
      subst compactSize
      subst code
      rfl
  | push value =>
      cases hWidth : pushWidthAt? pinnedPushPcs sourcePc value with
      | none => simp [sourceInstrSizeAt?, hWidth] at hSize
      | some width =>
          simp [sourceInstrSizeAt?, hWidth, emitSourceBlock?, emitInstrRev?]
            at hSize hCode
          subst compactSize
          subst code
          rfl
  | pushLabel target =>
      simp [sourceInstrSizeAt?] at hSize
  | jump target | jumpi target =>
      cases hDest : lookupLabel? table target with
      | none => simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some dest =>
          by_cases hFits : fitsWidth? branchWidth dest = true
          · simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?,
              hDest, hFits] at hSize hCode
            subst compactSize
            subst code
            simp [Program.codeByteLength, Instr.byteSize, Nat.add_assoc]
          · simp [emitSourceBlock?, emitInstrRev?, hDest, hFits] at hCode
  | jumpDynamic =>
      simp [sourceInstrSizeAt?] at hSize

def BoundaryPair (blocks : List SourceBlock)
    (sourceEnd compactEnd sourcePc compactPc : Nat) : Prop :=
  (∃ block,
    block ∈ blocks ∧ block.sourcePc = sourcePc ∧
      block.compactPc = compactPc) ∨
  (sourcePc = sourceEnd ∧ compactPc = compactEnd)

theorem BlocksValidFrom.next_boundary
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source
      sourcePc compactPc blocks) :
    forall {block : SourceBlock}, block ∈ blocks ->
      ∀ {compactSize : Nat},
        sourceInstrSizeAt? pinnedPushPcs branchWidth block.sourcePc
          block.sourceInstr = some compactSize ->
        BoundaryPair blocks
          (sourcePc + source.byteLength)
          (compactPc + Program.codeByteLength (blocksCode blocks))
          (block.sourcePc + block.sourceInstr.byteSize)
          (block.compactPc + compactSize) := by
  intro block hMem compactSize hSize
  induction hValid generalizing block compactSize with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc headSize code blocks
      hHeadSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          have hSizeEq : compactSize = headSize := by
            rw [hHeadSize] at hSize
            exact (Option.some.inj hSize).symm
          subst compactSize
          cases hRest with
          | nil =>
              right
              constructor
              · simp [Assembly.Program.byteLength, Assembly.Instr.byteSize_pos]
              · have hCodeLength :=
                    emitSourceBlock?_codeByteLength hHeadSize hCode
                simp [blocksCode, Program.codeByteLength, hCodeLength]
          | @cons next rest' _ _ nextSize nextCode
              nextBlocks hNextSize hNextCode hNextRest =>
              left
              refine
                ⟨{ sourcePc := sourcePc + instr.byteSize
                   compactPc := compactPc + headSize
                   sourceInstr := next
                   code := nextCode }, ?_, ?_, ?_⟩
              · simp
              · rfl
              · rfl
      | inr hTail =>
          have hTailBoundary := ih hTail hSize
          have hHeadCodeLength :=
            emitSourceBlock?_codeByteLength hHeadSize hCode
          rcases hTailBoundary with hNext | hEnd
          · left
            rcases hNext with ⟨next, hNextMem, hSource, hCompact⟩
            exact ⟨next, by simp [hNextMem], hSource, hCompact⟩
          · right
            rcases hEnd with ⟨hSourceEnd, hCompactEnd⟩
            constructor
            · simpa [Assembly.Program.byteLength_cons,
                Nat.add_assoc] using hSourceEnd
            · simpa [blocksCode, Program.codeByteLength_append,
                hHeadCodeLength, Nat.add_assoc] using hCompactEnd

theorem BlocksValidFrom.initial_boundary
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {blocks : List SourceBlock}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source 0 0
      blocks) :
    BoundaryPair blocks source.byteLength
      (Program.codeByteLength (blocksCode blocks)) 0 0 := by
  cases hValid with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest =>
      exact
        Or.inl
          ⟨{ sourcePc := 0
             compactPc := 0
             sourceInstr := instr
             code := code }, by simp⟩

theorem BlocksValidFrom.block_emit_of_mem
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source
      sourcePc compactPc blocks) :
    forall {block : SourceBlock}, block ∈ blocks ->
      ∃ compactSize,
        sourceInstrSizeAt? pinnedPushPcs branchWidth block.sourcePc
            block.sourceInstr = some compactSize ∧
          emitSourceBlock? pinnedPushPcs branchWidth block.sourcePc
            block.compactPc table
            block.sourceInstr = some block.code := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨compactSize, hSize, hCode⟩
      | inr hTail => exact ih hTail

theorem BlocksValidFrom.sourceInstr_mem_of_block_mem
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source
      sourcePc compactPc blocks) :
    forall {block : SourceBlock}, block ∈ blocks ->
      block.sourceInstr ∈ source := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          simp
      | inr hTail =>
          simp [ih hTail]

theorem BlocksValidFrom.decompose_of_block_mem
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source
      sourcePc compactPc blocks) :
    ∀ {block : SourceBlock}, block ∈ blocks ->
      ∃ pre post,
        source = pre ++ block.sourceInstr :: post ∧
          block.sourcePc = sourcePc + pre.byteLength := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨[], rest, rfl, by simp⟩
      | inr hTail =>
          obtain ⟨pre, post, hRest, hPc⟩ := ih hTail
          subst rest
          refine ⟨instr :: pre, post, by simp, ?_⟩
          simpa [Assembly.Program.byteLength_cons, Nat.add_assoc] using hPc

theorem instrAtPcFrom_end_eq_none
    (program : Assembly.Program) (base : Nat) :
    Assembly.Program.instrAtPcFrom program base
      (base + program.byteLength) = none := by
  induction program generalizing base with
  | nil => simp [Assembly.Program.instrAtPcFrom]
  | cons instr rest ih =>
      unfold Assembly.Program.instrAtPcFrom
      have hNe :
          base + Assembly.Program.byteLength (instr :: rest) ≠ base := by
        have hPositive := Assembly.Program.byteLength_pos_of_cons instr rest
        omega
      rw [if_neg hNe]
      simpa [Assembly.Program.byteLength_cons, Nat.add_assoc] using
        (ih (base + instr.byteSize))

theorem instrAtPc_end_eq_none (program : Assembly.Program) :
    program.instrAtPc program.byteLength = none := by
  simpa [Assembly.Program.instrAtPc] using
    instrAtPcFrom_end_eq_none program 0

theorem BlocksValidFrom.block_of_instrAtPcFrom
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc query pc : Nat}
    {blocks : List SourceBlock} {instr : Assembly.Instr}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source
      sourcePc compactPc blocks)
    (hAt : Assembly.Program.instrAtPcFrom source sourcePc query =
      some (pc, instr)) :
    ∃ block,
      block ∈ blocks ∧ block.sourcePc = pc ∧ block.sourceInstr = instr := by
  induction hValid with
  | nil => simp [Assembly.Program.instrAtPcFrom] at hAt
  | @cons head rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      unfold Assembly.Program.instrAtPcFrom at hAt
      split at hAt
      · simp at hAt
        rcases hAt with ⟨hPc, hInstr⟩
        subst pc
        subst instr
        exact
          ⟨{ sourcePc := sourcePc
             compactPc := compactPc
             sourceInstr := head
             code := code }, by simp⟩
      · obtain ⟨block, hMem, hBlockPc, hInstr⟩ := ih hAt
        exact ⟨block, by simp [hMem], hBlockPc, hInstr⟩

theorem BlocksValidFrom.block_of_instrAtPc
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {blocks : List SourceBlock}
    {query pc : Nat} {instr : Assembly.Instr}
    (hValid : BlocksValidFrom pinnedPushPcs branchWidth table source 0 0
      blocks)
    (hAt : source.instrAtPc query = some (pc, instr)) :
    ∃ block,
      block ∈ blocks ∧ block.sourcePc = pc ∧ block.sourceInstr = instr := by
  exact hValid.block_of_instrAtPcFrom hAt

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

theorem decodingCorrectOfWellFormedWithSuffix
    {program : Program}
    (hValid : program.Valid)
    (hLayout : Program.codeLayoutFrom program.code 0)
    (hWindow :
      Program.codeByteLength program.code < 18446744073709551616)
    (suffix : List UInt8) :
    DecodingCorrect program
      (Bytecode.ofList (program.code.flatMap encodeLocated ++ suffix)) where
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
    have hDecoded :=
      codeLayoutDecodeAtWithPrefix
        (code := program.code) (pre := []) (suffix := suffix) (base := 0)
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
    simpa [Bytecode.ofList] using hDecoded

/-- Remove an unconditional transfer to the label physically adjacent to it.
The label remains available to every other incoming edge. -/
def elideFallthroughJumpsRev :
    Assembly.Program → Assembly.Program → Assembly.Program
  | .jump target :: .label next :: rest, acc =>
      if target = next then
        elideFallthroughJumpsRev rest (.label next :: acc)
      else
        elideFallthroughJumpsRev
          rest (.label next :: .jump target :: acc)
  | instr :: rest, acc =>
      elideFallthroughJumpsRev rest (instr :: acc)
  | [], acc => acc.reverse

def elideFallthroughJumpsFast (source : Assembly.Program) :
    Assembly.Program :=
  elideFallthroughJumpsRev source []

@[implemented_by elideFallthroughJumpsFast]
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

def referencedLabelsRev : Assembly.Program → List Label → List Label
  | [], acc => acc.reverse
  | .pushLabel target :: rest, acc =>
      referencedLabelsRev rest (target :: acc)
  | .jump target :: rest, acc =>
      referencedLabelsRev rest (target :: acc)
  | .jumpi target :: rest, acc =>
      referencedLabelsRev rest (target :: acc)
  | _ :: rest, acc => referencedLabelsRev rest acc

def referencedLabelsFast (source : Assembly.Program) : List Label :=
  referencedLabelsRev source []

@[implemented_by referencedLabelsFast]
def referencedLabels (source : Assembly.Program) : List Label :=
  source.flatMap Assembly.Instr.targets

def referencedLabelSet (targets : List Label) : Std.HashSet Label :=
  targets.foldl (fun set label => set.insert label)
    (Std.HashSet.emptyWithCapacity targets.length)

def pruneUnreferencedLabelsRev (targets : Std.HashSet Label) :
    Assembly.Program → Assembly.Program → Assembly.Program
  | [], acc => acc.reverse
  | .label name :: rest, acc =>
      if targets.contains name then
        pruneUnreferencedLabelsRev targets rest (.label name :: acc)
      else
        pruneUnreferencedLabelsRev targets rest acc
  | instr :: rest, acc =>
      pruneUnreferencedLabelsRev targets rest (instr :: acc)

def pruneUnreferencedLabelsFast (targets : List Label)
    (source : Assembly.Program) : Assembly.Program :=
  pruneUnreferencedLabelsRev (referencedLabelSet targets) source []

@[implemented_by pruneUnreferencedLabelsFast]
def pruneUnreferencedLabels (targets : List Label) :
    Assembly.Program -> Assembly.Program
  | [] => []
  | .label name :: rest =>
      if name ∈ targets then
        .label name :: pruneUnreferencedLabels targets rest
      else
        pruneUnreferencedLabels targets rest
  | instr :: rest => instr :: pruneUnreferencedLabels targets rest

def prepareFast (source : Assembly.Program) : Assembly.Program :=
  let elided := elideFallthroughJumpsFast source
  pruneUnreferencedLabelsFast (referencedLabelsFast elided) elided

@[implemented_by prepareFast]
def prepare (source : Assembly.Program) : Assembly.Program :=
  let elided := elideFallthroughJumps source
  pruneUnreferencedLabels (referencedLabels elided) elided

private theorem elideFallthroughJumpsRev_eq
    (source acc : Assembly.Program) :
    elideFallthroughJumpsRev source acc =
      acc.reverse ++ elideFallthroughJumps source := by
  induction source generalizing acc with
  | nil => simp [elideFallthroughJumpsRev, elideFallthroughJumps]
  | cons instr rest ih =>
      cases instr with
      | jump target =>
          cases rest with
          | nil =>
              simp [elideFallthroughJumpsRev, elideFallthroughJumps]
          | cons next tail =>
              cases next with
              | label next =>
                  by_cases h : target = next
                  · have hIH := ih acc
                    simpa [elideFallthroughJumpsRev,
                      elideFallthroughJumps, h] using hIH
                  · have hIH := ih (.jump target :: acc)
                    simpa [elideFallthroughJumpsRev,
                      elideFallthroughJumps, h,
                      List.reverse_cons, List.append_assoc] using hIH
              | prim op | push op | pushLabel op | jump op | jumpi op |
                  jumpDynamic =>
                  have hIH := ih (.jump target :: acc)
                  simpa [elideFallthroughJumpsRev,
                    elideFallthroughJumps,
                    List.reverse_cons, List.append_assoc] using hIH
      | label name | prim name | push name | pushLabel name | jumpi name |
          jumpDynamic =>
          simp [elideFallthroughJumpsRev, elideFallthroughJumps, ih,
            List.reverse_cons, List.append_assoc]

theorem elideFallthroughJumpsFast_eq (source : Assembly.Program) :
    elideFallthroughJumpsFast source = elideFallthroughJumps source := by
  simp [elideFallthroughJumpsFast, elideFallthroughJumpsRev_eq]

private theorem referencedLabelsRev_eq (source : Assembly.Program)
    (acc : List Label) :
    referencedLabelsRev source acc =
      acc.reverse ++ referencedLabels source := by
  induction source generalizing acc with
  | nil => simp [referencedLabelsRev, referencedLabels]
  | cons instr rest ih =>
      cases instr <;>
        simp [referencedLabelsRev, referencedLabels,
          Assembly.Instr.targets, ih, List.reverse_cons, List.append_assoc]

theorem referencedLabelsFast_eq (source : Assembly.Program) :
    referencedLabelsFast source = referencedLabels source := by
  simp [referencedLabelsFast, referencedLabelsRev_eq]

private theorem hashSetContains_foldl_insert
    (items : List Label) (labels : Std.HashSet Label) (label : Label) :
    (items.foldl (fun set item => set.insert item) labels).contains label =
      (labels.contains label || items.contains label) := by
  induction items generalizing labels with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl, ih, Std.HashSet.contains_insert]
      by_cases hEq : head = label
      · subst head
        simp [Bool.or_comm]
      · have hRev : label ≠ head := by
          intro h
          exact hEq h.symm
        have hBeq : (head == label) = false :=
          beq_eq_false_iff_ne.mpr hEq
        simp [hBeq, hRev]

theorem referencedLabelSet_contains (targets : List Label) (label : Label) :
    (referencedLabelSet targets).contains label = targets.contains label := by
  simp [referencedLabelSet, hashSetContains_foldl_insert]

private theorem pruneUnreferencedLabelsRev_eq (targetList : List Label)
    (targetSet : Std.HashSet Label)
    (hSet : ∀ label, targetSet.contains label = targetList.contains label) :
    ∀ (source acc : Assembly.Program),
      pruneUnreferencedLabelsRev targetSet source acc =
        acc.reverse ++ pruneUnreferencedLabels targetList source
  | [], acc => by
      simp [pruneUnreferencedLabelsRev, pruneUnreferencedLabels]
  | instr :: rest, acc => by
      cases instr with
      | label name =>
          by_cases hMem : name ∈ targetList
          · have hContains : targetSet.contains name = true := by
              rw [hSet]
              simpa using hMem
            simp [pruneUnreferencedLabelsRev, pruneUnreferencedLabels,
              hMem, hContains,
              pruneUnreferencedLabelsRev_eq targetList targetSet hSet rest,
              List.reverse_cons, List.append_assoc]
          · have hContains : targetSet.contains name = false := by
              rw [hSet]
              simpa using hMem
            simp [pruneUnreferencedLabelsRev, pruneUnreferencedLabels,
              hMem, hContains,
              pruneUnreferencedLabelsRev_eq targetList targetSet hSet rest]
      | prim op | push op | pushLabel op | jump op | jumpi op | jumpDynamic =>
          simp [pruneUnreferencedLabelsRev, pruneUnreferencedLabels,
            pruneUnreferencedLabelsRev_eq targetList targetSet hSet rest,
            List.reverse_cons, List.append_assoc]

theorem pruneUnreferencedLabelsFast_eq
    (targets : List Label) (source : Assembly.Program) :
    pruneUnreferencedLabelsFast targets source =
      pruneUnreferencedLabels targets source := by
  unfold pruneUnreferencedLabelsFast
  rw [pruneUnreferencedLabelsRev_eq targets (referencedLabelSet targets)
    (referencedLabelSet_contains targets)]
  simp

theorem prepareFast_eq (source : Assembly.Program) :
    prepareFast source = prepare source := by
  simp [prepareFast, prepare, elideFallthroughJumpsFast_eq,
    referencedLabelsFast_eq, pruneUnreferencedLabelsFast_eq]

/-- Find physical Assembly push sites whose values differ between two
shape-identical programs. Pinning precisely these PCs gives both programs the
same compact layout while leaving every unrelated push minimum-width. -/
def differingPushPcsFrom? : Assembly.Program → Assembly.Program → Nat →
    Option (List Nat)
  | [], [], _ => some []
  | .push actual :: actualRest, .push marker :: markerRest, sourcePc => do
      let rest ← differingPushPcsFrom? actualRest markerRest
        (sourcePc + (Assembly.Instr.push actual).byteSize)
      if actual = marker then some rest else some (sourcePc :: rest)
  | actual :: actualRest, marker :: markerRest, sourcePc =>
      if actual = marker then
        differingPushPcsFrom? actualRest markerRest
          (sourcePc + actual.byteSize)
      else
        none
  | _, _, _ => none

def differingPushPcs? (actual marker : Assembly.Program) : Option (List Nat) :=
  differingPushPcsFrom? (prepare actual) (prepare marker) 0

inductive PreparationAction where
  | keep
  | skip
  deriving BEq, DecidableEq, Repr

structure PreparationBlock where
  sourcePc : Nat
  preparedPc : Nat
  sourceInstr : Assembly.Instr
  action : PreparationAction
  deriving DecidableEq, Repr

def alignPreparationFromRev? : Assembly.Program → Assembly.Program →
    Nat → Nat → List PreparationBlock → Option (List PreparationBlock)
  | [], [], _, _, acc => some acc.reverse
  | [], _ :: _, _, _, _ => none
  | instr :: rest, [], sourcePc, preparedPc, acc =>
      alignPreparationFromRev? rest []
        (sourcePc + instr.byteSize) preparedPc
        ({ sourcePc := sourcePc
           preparedPc := preparedPc
           sourceInstr := instr
           action := .skip } :: acc)
  | instr :: rest, preparedInstr :: preparedRest,
      sourcePc, preparedPc, acc =>
      if instr = preparedInstr then
        alignPreparationFromRev? rest preparedRest
          (sourcePc + instr.byteSize)
          (preparedPc + preparedInstr.byteSize)
          ({ sourcePc := sourcePc
             preparedPc := preparedPc
             sourceInstr := instr
             action := .keep } :: acc)
      else
        alignPreparationFromRev? rest (preparedInstr :: preparedRest)
          (sourcePc + instr.byteSize) preparedPc
          ({ sourcePc := sourcePc
             preparedPc := preparedPc
             sourceInstr := instr
             action := .skip } :: acc)

def alignPreparationFromFast? (source prepared : Assembly.Program)
    (sourcePc preparedPc : Nat) : Option (List PreparationBlock) :=
  alignPreparationFromRev? source prepared sourcePc preparedPc []

@[implemented_by alignPreparationFromFast?]
def alignPreparationFrom? : Assembly.Program -> Assembly.Program ->
    Nat -> Nat -> Option (List PreparationBlock)
  | [], [], _, _ => some []
  | [], _ :: _, _, _ => none
  | instr :: rest, [], sourcePc, preparedPc => do
      let blocks <- alignPreparationFrom? rest []
        (sourcePc + instr.byteSize) preparedPc
      some
        ({ sourcePc := sourcePc
           preparedPc := preparedPc
           sourceInstr := instr
           action := .skip } :: blocks)
  | instr :: rest, preparedInstr :: preparedRest, sourcePc, preparedPc =>
      if instr = preparedInstr then do
        let blocks <- alignPreparationFrom? rest preparedRest
          (sourcePc + instr.byteSize) (preparedPc + preparedInstr.byteSize)
        some
          ({ sourcePc := sourcePc
             preparedPc := preparedPc
             sourceInstr := instr
             action := .keep } :: blocks)
      else do
        let blocks <- alignPreparationFrom? rest
          (preparedInstr :: preparedRest)
          (sourcePc + instr.byteSize) preparedPc
        some
          ({ sourcePc := sourcePc
             preparedPc := preparedPc
             sourceInstr := instr
             action := .skip } :: blocks)
termination_by source prepared => source.length + prepared.length

def alignPreparationFast? (source prepared : Assembly.Program) :
    Option (List PreparationBlock) :=
  alignPreparationFromFast? source prepared 0 0

@[implemented_by alignPreparationFast?]
def alignPreparation? (source prepared : Assembly.Program) :
    Option (List PreparationBlock) :=
  alignPreparationFrom? source prepared 0 0

private theorem alignPreparationFromRev_eq :
    ∀ (source prepared : Assembly.Program) (sourcePc preparedPc : Nat)
      (acc : List PreparationBlock),
      alignPreparationFromRev? source prepared sourcePc preparedPc acc = do
        let blocks ← alignPreparationFrom? source prepared sourcePc preparedPc
        some (acc.reverse ++ blocks)
  | [], prepared, sourcePc, preparedPc, acc => by
      cases prepared <;>
        simp [alignPreparationFromRev?, alignPreparationFrom?]
  | instr :: rest, prepared, sourcePc, preparedPc, acc => by
      cases prepared with
      | nil =>
          simp [alignPreparationFromRev?, alignPreparationFrom?,
            alignPreparationFromRev_eq, List.reverse_cons,
            List.append_assoc]
          cases hTail :
              alignPreparationFrom? rest []
                (sourcePc + instr.byteSize) preparedPc <;> simp [hTail]
      | cons preparedInstr preparedRest =>
          by_cases hEq : instr = preparedInstr
          · subst instr
            simp [alignPreparationFromRev?, alignPreparationFrom?,
              alignPreparationFromRev_eq, List.reverse_cons,
              List.append_assoc]
            cases hTail :
                alignPreparationFrom? rest preparedRest
                  (sourcePc + preparedInstr.byteSize)
                  (preparedPc + preparedInstr.byteSize) <;> simp [hTail]
          · simp [alignPreparationFromRev?, alignPreparationFrom?, hEq,
              alignPreparationFromRev_eq, List.reverse_cons,
              List.append_assoc]
            cases hTail :
                alignPreparationFrom? rest (preparedInstr :: preparedRest)
                  (sourcePc + instr.byteSize) preparedPc <;> simp [hTail]

theorem alignPreparationFromFast_eq (source prepared : Assembly.Program)
    (sourcePc preparedPc : Nat) :
    alignPreparationFromFast? source prepared sourcePc preparedPc =
      alignPreparationFrom? source prepared sourcePc preparedPc := by
  simp [alignPreparationFromFast?, alignPreparationFromRev_eq]

theorem alignPreparationFast_eq (source prepared : Assembly.Program) :
    alignPreparationFast? source prepared =
      alignPreparation? source prepared := by
  simp [alignPreparationFast?, alignPreparation?, alignPreparationFromFast_eq]

def PreparationBoundaryPair (blocks : List PreparationBlock)
    (sourceEnd preparedEnd sourcePc preparedPc : Nat) : Prop :=
  (∃ block,
    block ∈ blocks ∧ block.sourcePc = sourcePc ∧
      block.preparedPc = preparedPc) ∨
  (sourcePc = sourceEnd ∧ preparedPc = preparedEnd)

inductive PreparationBlocksValidFrom :
    Assembly.Program -> Assembly.Program -> Nat -> Nat ->
      List PreparationBlock -> Prop
  | nil (sourcePc preparedPc : Nat) :
      PreparationBlocksValidFrom [] [] sourcePc preparedPc []
  | keep (instr : Assembly.Instr)
      (sourceRest preparedRest : Assembly.Program)
      (sourcePc preparedPc : Nat) (blocks : List PreparationBlock)
      (hRest : PreparationBlocksValidFrom sourceRest preparedRest
        (sourcePc + instr.byteSize) (preparedPc + instr.byteSize) blocks) :
      PreparationBlocksValidFrom (instr :: sourceRest)
        (instr :: preparedRest) sourcePc preparedPc
        ({ sourcePc := sourcePc
           preparedPc := preparedPc
           sourceInstr := instr
           action := .keep } :: blocks)
  | skip (instr : Assembly.Instr) (sourceRest prepared : Assembly.Program)
      (sourcePc preparedPc : Nat) (blocks : List PreparationBlock)
      (hRest : PreparationBlocksValidFrom sourceRest prepared
        (sourcePc + instr.byteSize) preparedPc blocks) :
      PreparationBlocksValidFrom (instr :: sourceRest) prepared
        sourcePc preparedPc
        ({ sourcePc := sourcePc
           preparedPc := preparedPc
           sourceInstr := instr
           action := .skip } :: blocks)

theorem PreparationBlocksValidFrom.prepared_byteLength_le_source_byteLength
    {source prepared : Assembly.Program} {sourcePc preparedPc : Nat}
    {blocks : List PreparationBlock}
    (hValid : PreparationBlocksValidFrom source prepared
      sourcePc preparedPc blocks) :
    prepared.byteLength ≤ source.byteLength := by
  induction hValid with
  | nil => simp
  | keep instr sourceRest preparedRest sourcePc preparedPc blocks hRest ih =>
      simp only [Assembly.Program.byteLength_cons]
      omega
  | skip instr sourceRest prepared sourcePc preparedPc blocks hRest ih =>
      simp only [Assembly.Program.byteLength_cons]
      omega

def PreparationBlock.nextPreparedPc (block : PreparationBlock) : Nat :=
  match block.action with
  | .keep => block.preparedPc + block.sourceInstr.byteSize
  | .skip => block.preparedPc

theorem PreparationBlocksValidFrom.initial_boundary
    {source prepared : Assembly.Program} {sourcePc preparedPc : Nat}
    {blocks : List PreparationBlock}
    (hValid : PreparationBlocksValidFrom source prepared
      sourcePc preparedPc blocks) :
    PreparationBoundaryPair blocks
      (sourcePc + source.byteLength) (preparedPc + prepared.byteLength)
      sourcePc preparedPc := by
  cases hValid with
  | nil => exact Or.inr ⟨by simp, by simp⟩
  | keep instr sourceRest preparedRest sourcePc preparedPc blocks hRest =>
      exact Or.inl
        ⟨{ sourcePc := sourcePc, preparedPc := preparedPc
           sourceInstr := instr, action := .keep }, by simp⟩
  | skip instr sourceRest prepared sourcePc preparedPc blocks hRest =>
      exact Or.inl
        ⟨{ sourcePc := sourcePc, preparedPc := preparedPc
           sourceInstr := instr, action := .skip }, by simp⟩

theorem PreparationBlocksValidFrom.next_boundary
    {source prepared : Assembly.Program} {sourcePc preparedPc : Nat}
    {blocks : List PreparationBlock}
    (hValid : PreparationBlocksValidFrom source prepared
      sourcePc preparedPc blocks) :
    ∀ {block : PreparationBlock}, block ∈ blocks ->
      PreparationBoundaryPair blocks
        (sourcePc + source.byteLength) (preparedPc + prepared.byteLength)
        (block.sourcePc + block.sourceInstr.byteSize)
        block.nextPreparedPc := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @keep instr sourceRest preparedRest sourcePc preparedPc blocks hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          cases hRest with
          | nil =>
              exact Or.inr ⟨by simp [Assembly.Program.byteLength_cons],
                by simp [Assembly.Program.byteLength_cons,
                  PreparationBlock.nextPreparedPc]⟩
          | keep next sourceTail preparedTail nextSourcePc nextPreparedPc
              nextBlocks hNext =>
              exact Or.inl
                ⟨{ sourcePc := sourcePc + instr.byteSize
                   preparedPc := preparedPc + instr.byteSize
                   sourceInstr := next, action := .keep },
                  by simp [PreparationBlock.nextPreparedPc]⟩
          | skip next sourceTail prepared nextSourcePc nextPreparedPc
              nextBlocks hNext =>
              exact Or.inl
                ⟨{ sourcePc := sourcePc + instr.byteSize
                   preparedPc := preparedPc + instr.byteSize
                   sourceInstr := next, action := .skip },
                  by simp [PreparationBlock.nextPreparedPc]⟩
      | inr hTail =>
          have hNext := ih hTail
          rcases hNext with hActive | hEnd
          · rcases hActive with ⟨next, hNextMem, hSource, hPrepared⟩
            exact Or.inl ⟨next, by simp [hNextMem], hSource, hPrepared⟩
          · exact Or.inr
              ⟨by simpa [Assembly.Program.byteLength_cons, Nat.add_assoc]
                  using hEnd.1,
                by simpa [Assembly.Program.byteLength_cons, Nat.add_assoc]
                  using hEnd.2⟩
  | @skip instr sourceRest prepared sourcePc preparedPc blocks hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          cases hRest with
          | nil =>
              exact Or.inr ⟨by simp [Assembly.Program.byteLength_cons],
                by simp [PreparationBlock.nextPreparedPc]⟩
          | keep next sourceTail preparedTail nextSourcePc nextPreparedPc
              nextBlocks hNext =>
              exact Or.inl
                ⟨{ sourcePc := sourcePc + instr.byteSize
                   preparedPc := preparedPc
                   sourceInstr := next, action := .keep },
                  by simp [PreparationBlock.nextPreparedPc]⟩
          | skip next sourceTail prepared nextSourcePc nextPreparedPc
              nextBlocks hNext =>
              exact Or.inl
                ⟨{ sourcePc := sourcePc + instr.byteSize
                   preparedPc := preparedPc
                   sourceInstr := next, action := .skip },
                  by simp [PreparationBlock.nextPreparedPc]⟩
      | inr hTail =>
          have hNext := ih hTail
          rcases hNext with hActive | hEnd
          · rcases hActive with ⟨next, hNextMem, hSource, hPrepared⟩
            exact Or.inl ⟨next, by simp [hNextMem], hSource, hPrepared⟩
          · exact Or.inr
              ⟨by simpa [Assembly.Program.byteLength_cons, Nat.add_assoc]
                  using hEnd.1,
                hEnd.2⟩

theorem PreparationBlocksValidFrom.source_decompose_of_block_mem
    {source prepared : Assembly.Program} {sourcePc preparedPc : Nat}
    {blocks : List PreparationBlock}
    (hValid : PreparationBlocksValidFrom source prepared
      sourcePc preparedPc blocks) :
    ∀ {block : PreparationBlock}, block ∈ blocks ->
      ∃ pre post,
        source = pre ++ block.sourceInstr :: post ∧
          block.sourcePc = sourcePc + pre.byteLength := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @keep instr sourceRest preparedRest sourcePc preparedPc blocks hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨[], sourceRest, rfl, by simp⟩
      | inr hTail =>
          obtain ⟨pre, post, hSource, hPc⟩ := ih hTail
          subst sourceRest
          refine ⟨instr :: pre, post, by simp, ?_⟩
          simpa [Assembly.Program.byteLength_cons, Nat.add_assoc] using hPc
  | @skip instr sourceRest prepared sourcePc preparedPc blocks hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨[], sourceRest, rfl, by simp⟩
      | inr hTail =>
          obtain ⟨pre, post, hSource, hPc⟩ := ih hTail
          subst sourceRest
          refine ⟨instr :: pre, post, by simp, ?_⟩
          simpa [Assembly.Program.byteLength_cons, Nat.add_assoc] using hPc

theorem PreparationBlocksValidFrom.prepared_decompose_of_keep
    {source prepared : Assembly.Program} {sourcePc preparedPc : Nat}
    {blocks : List PreparationBlock}
    (hValid : PreparationBlocksValidFrom source prepared
      sourcePc preparedPc blocks) :
    ∀ {block : PreparationBlock}, block ∈ blocks -> block.action = .keep ->
      ∃ pre post,
        prepared = pre ++ block.sourceInstr :: post ∧
          block.preparedPc = preparedPc + pre.byteLength := by
  intro block hMem hKeep
  induction hValid with
  | nil => simp at hMem
  | @keep instr sourceRest preparedRest sourcePc preparedPc blocks hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨[], preparedRest, rfl, by simp⟩
      | inr hTail =>
          obtain ⟨pre, post, hPrepared, hPc⟩ := ih hTail
          subst preparedRest
          refine ⟨instr :: pre, post, by simp, ?_⟩
          simpa [Assembly.Program.byteLength_cons, Nat.add_assoc] using hPc
  | @skip instr sourceRest prepared sourcePc preparedPc blocks hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          simp at hKeep
      | inr hTail => exact ih hTail

theorem alignPreparationFrom?_valid :
    ∀ {source prepared : Assembly.Program} {sourcePc preparedPc : Nat}
      {blocks : List PreparationBlock},
      alignPreparationFrom? source prepared sourcePc preparedPc = some blocks ->
        PreparationBlocksValidFrom source prepared sourcePc preparedPc blocks := by
  intro source
  induction source with
  | nil =>
      intro prepared sourcePc preparedPc blocks hAlign
      cases prepared with
      | nil =>
          simp [alignPreparationFrom?] at hAlign
          subst blocks
          exact .nil sourcePc preparedPc
      | cons preparedInstr preparedRest =>
          simp [alignPreparationFrom?] at hAlign
  | cons instr rest ih =>
      intro prepared sourcePc preparedPc blocks hAlign
      cases prepared with
      | nil =>
          simp [alignPreparationFrom?] at hAlign
          cases hRest : alignPreparationFrom? rest []
              (sourcePc + instr.byteSize) preparedPc with
          | none => simp [hRest] at hAlign
          | some restBlocks =>
              simp [hRest] at hAlign
              subst blocks
              exact .skip instr rest [] sourcePc preparedPc restBlocks
                (ih hRest)
      | cons preparedInstr preparedRest =>
          by_cases hEq : instr = preparedInstr
          · subst preparedInstr
            simp [alignPreparationFrom?] at hAlign
            cases hRest : alignPreparationFrom? rest preparedRest
                (sourcePc + instr.byteSize) (preparedPc + instr.byteSize) with
            | none => simp [hRest] at hAlign
            | some restBlocks =>
                simp [hRest] at hAlign
                subst blocks
                exact .keep instr rest preparedRest sourcePc preparedPc
                  restBlocks (ih hRest)
          · simp [alignPreparationFrom?, hEq] at hAlign
            cases hRest : alignPreparationFrom? rest
                (preparedInstr :: preparedRest)
                (sourcePc + instr.byteSize) preparedPc with
            | none => simp [hRest] at hAlign
            | some restBlocks =>
                simp [hRest] at hAlign
                subst blocks
                exact .skip instr rest (preparedInstr :: preparedRest)
                  sourcePc preparedPc restBlocks (ih hRest)

theorem alignPreparation?_valid
    {source prepared : Assembly.Program} {blocks : List PreparationBlock}
    (hAlign : alignPreparation? source prepared = some blocks) :
    PreparationBlocksValidFrom source prepared 0 0 blocks := by
  exact alignPreparationFrom?_valid hAlign

def preparationTargetPc? (blocks : List PreparationBlock)
    (sourceEnd preparedEnd sourcePc : Nat) : Option Nat :=
  match blocks.find? fun block => block.sourcePc == sourcePc with
  | some block => some block.preparedPc
  | none => if sourcePc = sourceEnd then some preparedEnd else none

abbrev LabelPcIndex := Std.HashMap Label Nat
abbrev BoundaryPcIndex := Std.HashMap Nat Nat

def buildLabelPcIndexFrom : Assembly.Program -> Nat -> LabelPcIndex ->
    LabelPcIndex
  | [], _pc, index => index
  | instr :: rest, pc, index =>
      let index :=
        match instr with
        | .label name => index.insertIfNew name pc
        | _ => index
      buildLabelPcIndexFrom rest (pc + instr.byteSize) index

def buildLabelPcIndex (program : Assembly.Program) : LabelPcIndex :=
  buildLabelPcIndexFrom program 0 {}

theorem buildLabelPcIndexFrom_get?
    (program : Assembly.Program) (pc : Nat) (index : LabelPcIndex)
    (target : Label) :
    (buildLabelPcIndexFrom program pc index).get? target =
      match index.get? target with
      | some existing => some existing
      | none => Assembly.Program.labelPcFrom program pc target := by
  induction program generalizing pc index with
  | nil =>
      cases hExisting : index.get? target <;>
        simp only [buildLabelPcIndexFrom, Assembly.Program.labelPcFrom,
          hExisting]
  | cons instr rest ih =>
      cases instr with
      | label name =>
          rw [buildLabelPcIndexFrom, ih]
          by_cases hName : name = target
          · subst name
            cases hExisting : index.get? target with
            | none =>
                have hExisting' : index[target]? = none := by
                  simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
                have hNotMem : target ∉ index := by
                  intro hMem
                  have hSome :=
                    (Std.HashMap.mem_iff_isSome_getElem?).mp hMem
                  rw [hExisting'] at hSome
                  simp at hSome
                simp only [Std.HashMap.get?_eq_getElem?,
                  Std.HashMap.getElem?_insertIfNew]
                simp [hExisting', hNotMem, Assembly.Program.labelPcFrom]
            | some existing =>
                have hExisting' : index[target]? = some existing := by
                  simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
                obtain ⟨hMem, _hGet⟩ :=
                  (Std.HashMap.getElem?_eq_some_iff.mp hExisting')
                simp only [Std.HashMap.get?_eq_getElem?,
                  Std.HashMap.getElem?_insertIfNew]
                simp only [beq_self_eq_true, true_and, hMem,
                  not_true_eq_false, if_false, hExisting']
          · have hBeq : (name == target) = false := by
              simpa using hName
            simp only [Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insertIfNew]
            simp [hBeq, hName, Assembly.Program.labelPcFrom]
      | prim op | push op | pushLabel op | jump op | jumpi op =>
          simpa [buildLabelPcIndexFrom, Assembly.Program.labelPcFrom]
            using ih (pc := pc + Assembly.Instr.byteSize _) (index := index)
      | jumpDynamic =>
          simpa [buildLabelPcIndexFrom, Assembly.Program.labelPcFrom]
            using ih
              (pc := pc + Assembly.Instr.byteSize .jumpDynamic)
              (index := index)

theorem buildLabelPcIndex_get?
    (program : Assembly.Program) (target : Label) :
    (buildLabelPcIndex program).get? target = program.labelPc target := by
  simpa [buildLabelPcIndex, Assembly.Program.labelPc] using
    buildLabelPcIndexFrom_get? program 0 ({} : LabelPcIndex) target

def buildBoundaryPcIndex : List PreparationBlock -> BoundaryPcIndex ->
    BoundaryPcIndex
  | [], index => index
  | block :: rest, index =>
      buildBoundaryPcIndex rest
        (index.insertIfNew block.sourcePc block.preparedPc)

def preparationBoundaryIndex (blocks : List PreparationBlock) :
    BoundaryPcIndex :=
  buildBoundaryPcIndex blocks {}

theorem buildBoundaryPcIndex_get?
    (blocks : List PreparationBlock) (index : BoundaryPcIndex)
    (query : Nat) :
    (buildBoundaryPcIndex blocks index).get? query =
      match index.get? query with
      | some existing => some existing
      | none =>
          (blocks.find? fun block => block.sourcePc == query).map
            PreparationBlock.preparedPc := by
  induction blocks generalizing index with
  | nil =>
      cases hExisting : index.get? query <;>
        simp only [buildBoundaryPcIndex, List.find?_nil, Option.map_none,
          hExisting]
  | cons block rest ih =>
      rw [buildBoundaryPcIndex, ih]
      by_cases hPc : block.sourcePc = query
      · subst query
        cases hExisting : index.get? block.sourcePc with
        | none =>
            have hExisting' : index[block.sourcePc]? = none := by
              simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
            have hNotMem : block.sourcePc ∉ index := by
              intro hMem
              have hSome :=
                (Std.HashMap.mem_iff_isSome_getElem?).mp hMem
              rw [hExisting'] at hSome
              simp at hSome
            simp only [Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insertIfNew]
            simp [hExisting', hNotMem]
        | some existing =>
            have hExisting' : index[block.sourcePc]? = some existing := by
              simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
            obtain ⟨hMem, _hGet⟩ :=
              (Std.HashMap.getElem?_eq_some_iff.mp hExisting')
            simp only [Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insertIfNew]
            simp only [beq_self_eq_true, true_and, hMem,
              not_true_eq_false, if_false, hExisting']
      · have hBeq : (block.sourcePc == query) = false := by
          simpa using hPc
        simp only [Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insertIfNew]
        simp [hBeq, hPc]

theorem preparationBoundaryIndex_get?
    (blocks : List PreparationBlock) (query : Nat) :
    (preparationBoundaryIndex blocks).get? query =
      (blocks.find? fun block => block.sourcePc == query).map
        PreparationBlock.preparedPc := by
  simpa [preparationBoundaryIndex] using
    buildBoundaryPcIndex_get? blocks ({} : BoundaryPcIndex) query

def preparationTargetPcIndexed? (index : BoundaryPcIndex)
    (sourceEnd preparedEnd sourcePc : Nat) : Option Nat :=
  match index.get? sourcePc with
  | some preparedPc => some preparedPc
  | none => if sourcePc = sourceEnd then some preparedEnd else none

theorem preparationTargetPcIndexed_eq
    (blocks : List PreparationBlock)
    (sourceEnd preparedEnd sourcePc : Nat) :
    preparationTargetPcIndexed? (preparationBoundaryIndex blocks)
        sourceEnd preparedEnd sourcePc =
      preparationTargetPc? blocks sourceEnd preparedEnd sourcePc := by
  unfold preparationTargetPcIndexed? preparationTargetPc?
  rw [preparationBoundaryIndex_get?]
  cases hFind : blocks.find? (fun block => block.sourcePc == sourcePc) <;>
    simp [hFind]

theorem preparationBoundaryPair_of_targetPc?
    {blocks : List PreparationBlock}
    {sourceEnd preparedEnd sourcePc preparedPc : Nat}
    (hLookup : preparationTargetPc? blocks sourceEnd preparedEnd sourcePc =
      some preparedPc) :
    PreparationBoundaryPair blocks sourceEnd preparedEnd sourcePc preparedPc := by
  unfold preparationTargetPc? at hLookup
  cases hFind : blocks.find? (fun block => block.sourcePc == sourcePc) with
  | some block =>
      have hMem := List.mem_of_find?_eq_some hFind
      have hSource := List.find?_some hFind
      rw [hFind] at hLookup
      simp at hLookup
      exact Or.inl ⟨block, hMem, by simpa using hSource, hLookup⟩
  | none =>
      rw [hFind] at hLookup
      by_cases hEnd : sourcePc = sourceEnd
      · simp [hEnd] at hLookup
        exact Or.inr ⟨hEnd, hLookup.symm⟩
      · simp [hEnd] at hLookup

def preparationBlockSafe? (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) (block : PreparationBlock) : Bool :=
  match block.action, block.sourceInstr with
  | .skip, .label _ => true
  | .skip, .jump target =>
      match source.labelPc target with
      | some sourceDest =>
          preparationTargetPc? blocks source.byteLength prepared.byteLength
            sourceDest == some block.preparedPc
      | none => false
  | .skip, _ => false
  | .keep, .jump target | .keep, .jumpi target =>
      match source.labelPc target, prepared.labelPc target with
      | some sourceDest, some preparedDest =>
          preparationTargetPc? blocks source.byteLength prepared.byteLength
            sourceDest == some preparedDest
      | _, _ => false
  | .keep, .pushLabel _ | .keep, .jumpDynamic => false
  | .keep, .prim .pc => false
  | .keep, _ => true

def preparationSafe? (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : Bool :=
  blocks.all (preparationBlockSafe? source prepared blocks)

structure PreparationLookupIndex where
  sourceLabels : LabelPcIndex
  preparedLabels : LabelPcIndex
  boundaries : BoundaryPcIndex

def buildPreparationLookupIndex (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : PreparationLookupIndex :=
  { sourceLabels := buildLabelPcIndex source
    preparedLabels := buildLabelPcIndex prepared
    boundaries := preparationBoundaryIndex blocks }

def preparationBlockSafeIndexed? (index : PreparationLookupIndex)
    (sourceEnd preparedEnd : Nat) (block : PreparationBlock) : Bool :=
  match block.action, block.sourceInstr with
  | .skip, .label _ => true
  | .skip, .jump target =>
      match index.sourceLabels.get? target with
      | some sourceDest =>
          preparationTargetPcIndexed? index.boundaries sourceEnd preparedEnd
            sourceDest == some block.preparedPc
      | none => false
  | .skip, _ => false
  | .keep, .jump target | .keep, .jumpi target =>
      match index.sourceLabels.get? target,
          index.preparedLabels.get? target with
      | some sourceDest, some preparedDest =>
          preparationTargetPcIndexed? index.boundaries sourceEnd preparedEnd
            sourceDest == some preparedDest
      | _, _ => false
  | .keep, .pushLabel _ | .keep, .jumpDynamic => false
  | .keep, .prim .pc => false
  | .keep, _ => true

def preparationSafeIndexed? (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : Bool :=
  let index := buildPreparationLookupIndex source prepared blocks
  blocks.all
    (preparationBlockSafeIndexed? index source.byteLength prepared.byteLength)

theorem preparationBlockSafeIndexed_eq
    (source prepared : Assembly.Program) (blocks : List PreparationBlock)
    (block : PreparationBlock) :
    preparationBlockSafeIndexed?
        (buildPreparationLookupIndex source prepared blocks)
        source.byteLength prepared.byteLength block =
      preparationBlockSafe? source prepared blocks block := by
  rcases block with ⟨sourcePc, preparedPc, sourceInstr, action⟩
  cases action <;> cases sourceInstr <;>
    simp [preparationBlockSafeIndexed?, preparationBlockSafe?,
      buildPreparationLookupIndex, buildLabelPcIndex_get?,
      preparationTargetPcIndexed_eq]
  all_goals try (rename_i op; cases op <;> rfl)
  all_goals
    simp only [← Std.HashMap.get?_eq_getElem?, buildLabelPcIndex_get?]

theorem preparationSafeIndexed_eq
    (source prepared : Assembly.Program) (blocks : List PreparationBlock) :
    preparationSafeIndexed? source prepared blocks =
      preparationSafe? source prepared blocks := by
  unfold preparationSafeIndexed? preparationSafe?
  apply congrArg (fun predicate => blocks.all predicate)
  funext block
  exact preparationBlockSafeIndexed_eq source prepared blocks block

def PreparationBlockSafe (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) (block : PreparationBlock) : Prop :=
  match block.action, block.sourceInstr with
  | .skip, .label _ => True
  | .skip, .jump target =>
      ∃ sourceDest,
        source.labelPc target = some sourceDest ∧
          preparationTargetPc? blocks source.byteLength prepared.byteLength
            sourceDest = some block.preparedPc
  | .skip, _ => False
  | .keep, .jump target | .keep, .jumpi target =>
      ∃ sourceDest preparedDest,
        source.labelPc target = some sourceDest ∧
          prepared.labelPc target = some preparedDest ∧
          preparationTargetPc? blocks source.byteLength prepared.byteLength
              sourceDest = some preparedDest
  | .keep, .pushLabel _ | .keep, .jumpDynamic => False
  | .keep, .prim .pc => False
  | .keep, _ => True

def PreparationSafe (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : Prop :=
  ∀ block, block ∈ blocks -> PreparationBlockSafe source prepared blocks block

theorem preparationBlockSafe_of_check
    {source prepared : Assembly.Program} {blocks : List PreparationBlock}
    {block : PreparationBlock}
    (hCheck : preparationBlockSafe? source prepared blocks block = true) :
    PreparationBlockSafe source prepared blocks block := by
  rcases block with ⟨sourcePc, preparedPc, sourceInstr, action⟩
  cases action <;> cases sourceInstr <;>
    simp [preparationBlockSafe?, PreparationBlockSafe] at hCheck ⊢
  all_goals
    split at hCheck <;> simp_all

theorem preparationSafe_of_check
    {source prepared : Assembly.Program} {blocks : List PreparationBlock}
    (hCheck : preparationSafe? source prepared blocks = true) :
    PreparationSafe source prepared blocks := by
  intro block hMem
  exact preparationBlockSafe_of_check
    ((List.all_eq_true.mp hCheck) block hMem)

structure Artifact where
  pinnedPushPcs : List Nat
  physicalSource : Assembly.Program
  branchWidth : Nat
  labels : LabelTable
  codeLength : Nat
  preparation : List PreparationBlock
  blocks : List SourceBlock
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
  | .pushLabel _ =>
      { stats with
        instructions := stats.instructions + 1
        pushes := stats.pushes + 1 }
  | .jump _ =>
      { stats with
        instructions := stats.instructions + 1
        jumps := stats.jumps + 1 }
  | .jumpi _ =>
      { stats with
        instructions := stats.instructions + 1
        jumpis := stats.jumpis + 1 }
  | .jumpDynamic =>
      { stats with
        instructions := stats.instructions + 1
        jumps := stats.jumps + 1 }
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

def compile? (source : Assembly.Program)
    (pinnedPushPcs : List Nat := []) : Option Artifact := do
  let _ <- if decide source.PCFits then some () else none
  let physicalSource := prepare source
  let preparation <- alignPreparation? source physicalSource
  let _ <- if preparationSafeIndexed? source physicalSource preparation then
    some ()
  else none
  let branchWidth <- branchWidthFor? pinnedPushPcs physicalSource
  let (labels, codeLength) <- layout? pinnedPushPcs physicalSource branchWidth
  let program <- emit? pinnedPushPcs physicalSource branchWidth labels
  let blocks <- emitBlocks? pinnedPushPcs physicalSource branchWidth labels
  if blocksCodeMatches? blocks program.code then
    if labelsConsistent? blocks labels then
      if program.wellFormed? then
        if Program.codeByteLength program.code + 1 < 18446744073709551616 then
          some
            { pinnedPushPcs := pinnedPushPcs
              physicalSource := physicalSource
              branchWidth := branchWidth
              labels := labels
              codeLength := codeLength
              preparation := preparation
              blocks := blocks
              program := program
              bytes := encode program }
        else none
      else
        none
    else
      none
  else
    none

structure Artifact.ValidFor (artifact : Artifact)
    (source : Assembly.Program) : Prop where
  sourcePCFits : source.PCFits
  physicalSource : artifact.physicalSource = prepare source
  preparationAligned : alignPreparation? source artifact.physicalSource =
    some artifact.preparation
  preparationSafeIndexed : preparationSafeIndexed? source artifact.physicalSource
    artifact.preparation = true
  selectedBranchWidth :
    branchWidthFor? artifact.pinnedPushPcs artifact.physicalSource =
    some artifact.branchWidth
  layout : layout? artifact.pinnedPushPcs artifact.physicalSource
    artifact.branchWidth =
    some (artifact.labels, artifact.codeLength)
  emitted : emit? artifact.pinnedPushPcs artifact.physicalSource
    artifact.branchWidth artifact.labels =
    some artifact.program
  blocks : emitBlocks? artifact.pinnedPushPcs artifact.physicalSource
    artifact.branchWidth artifact.labels = some artifact.blocks
  blockCode : blocksCode artifact.blocks = artifact.program.code
  labelsConsistent : LabelsConsistent artifact.blocks artifact.labels
  wellFormed : artifact.program.Valid ∧
    Program.codeLayoutFrom artifact.program.code 0 ∧
      Program.codeByteLength artifact.program.code < 18446744073709551616 ∧
        artifact.program.PCIndependent
  bytes : artifact.bytes = encode artifact.program
  sentinelFits : Program.codeByteLength artifact.program.code + 1 <
    18446744073709551616

theorem compile?_valid {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    artifact.ValidFor source := by
  unfold compile? at hCompile
  have hSourceFits : source.PCFits := by
    by_contra hNotFits
    simp [hNotFits] at hCompile
  simp [hSourceFits] at hCompile
  generalize hPhysical : prepare source = physicalSource at hCompile
  cases hPreparation : alignPreparation? source physicalSource with
  | none => simp [hPreparation] at hCompile
  | some preparation =>
      simp [hPreparation] at hCompile
      by_cases hPreparationSafe :
          preparationSafeIndexed? source physicalSource preparation = true
      · simp [hPreparationSafe] at hCompile
        cases hWidth : branchWidthFor? pinnedPushPcs physicalSource with
        | none => simp [hWidth] at hCompile
        | some branchWidth =>
            simp [hWidth] at hCompile
            cases hLayout : layout? pinnedPushPcs physicalSource branchWidth with
            | none => simp [hLayout] at hCompile
            | some layoutResult =>
                cases layoutResult with
                | mk labels codeLength =>
                    simp [hLayout] at hCompile
                    cases hEmit : emit? pinnedPushPcs physicalSource branchWidth labels with
                    | none => simp [hEmit] at hCompile
                    | some program =>
                        simp [hEmit] at hCompile
                        cases hBlocks :
                            emitBlocks? pinnedPushPcs physicalSource branchWidth labels with
                        | none => simp [hBlocks] at hCompile
                        | some blocks =>
                            simp [hBlocks] at hCompile
                            by_cases hCodeCheck :
                                blocksCodeMatches? blocks program.code = true
                            · have hCode :=
                                blocksCodeMatches_of_check hCodeCheck
                              simp [hCodeCheck] at hCompile
                              by_cases hLabels :
                                  labelsConsistent? blocks labels = true
                              · simp [hLabels] at hCompile
                                by_cases hWellFormed :
                                    program.wellFormed? = true
                                · simp [hWellFormed] at hCompile
                                  by_cases hSentinel :
                                      Program.codeByteLength program.code + 1 <
                                        18446744073709551616
                                  · simp [hSentinel] at hCompile
                                    cases hCompile
                                    exact Artifact.ValidFor.mk hSourceFits
                                      hPhysical.symm hPreparation
                                      hPreparationSafe hWidth hLayout hEmit
                                      hBlocks hCode
                                      (labelsConsistent_of_check hLabels)
                                      (Program.wellFormed_of_check hWellFormed)
                                      rfl hSentinel
                                  · simp [hSentinel] at hCompile
                                · simp [hWellFormed] at hCompile
                              · simp [hLabels] at hCompile
                            · simp [hCodeCheck] at hCompile
      · simp [hPreparationSafe] at hCompile

theorem Artifact.ValidFor.physicalSourcePCFits
    {artifact : Artifact} {source : Assembly.Program}
    (hValid : artifact.ValidFor source) :
    artifact.physicalSource.PCFits := by
  apply Assembly.Program.PCFits.of_byteLength_le hValid.sourcePCFits
  exact
    (alignPreparation?_valid hValid.preparationAligned).prepared_byteLength_le_source_byteLength

theorem compile?_preparationBlocksValid
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    PreparationBlocksValidFrom source artifact.physicalSource 0 0
      artifact.preparation := by
  exact alignPreparation?_valid (compile?_valid hCompile).preparationAligned

theorem compile?_preparationSafe
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    PreparationSafe source artifact.physicalSource artifact.preparation := by
  apply preparationSafe_of_check
  rw [← preparationSafeIndexed_eq]
  exact (compile?_valid hCompile).preparationSafeIndexed

theorem Artifact.ValidFor.mem_program_of_mem_block
    {artifact : Artifact} {source : Assembly.Program}
    (hValid : artifact.ValidFor source)
    {block : SourceBlock} (hBlock : block ∈ artifact.blocks)
    {located : Located} (hLocated : located ∈ block.code) :
    located ∈ artifact.program.code := by
  rw [← hValid.blockCode]
  unfold blocksCode
  exact List.mem_flatMap.mpr ⟨block, hBlock, hLocated⟩

theorem compile?_decodingCorrect
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    DecodingCorrect artifact.program artifact.bytes := by
  have hValid := compile?_valid hCompile
  rw [hValid.bytes]
  exact
    decodingCorrectOfWellFormed
      hValid.wellFormed.1 hValid.wellFormed.2.1 hValid.wellFormed.2.2.1

theorem compile?_decodingCorrect_with_suffix
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (suffix : List UInt8) :
    DecodingCorrect artifact.program
      (Bytecode.ofList (artifact.bytes.toList ++ suffix)) := by
  have hValid := compile?_valid hCompile
  rw [hValid.bytes]
  simpa [encode, Bytecode.ofList] using
    decodingCorrectOfWellFormedWithSuffix
      hValid.wellFormed.1 hValid.wellFormed.2.1
      hValid.wellFormed.2.2.1 suffix

theorem compile?_blocksValid
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    BlocksValidFrom artifact.pinnedPushPcs artifact.branchWidth artifact.labels
      artifact.physicalSource 0 0 artifact.blocks := by
  exact emitBlocks?_valid (compile?_valid hCompile).blocks

theorem compile?_block_of_instrAtPc
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {query pc : Nat} {instr : Assembly.Instr}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hAt : artifact.physicalSource.instrAtPc query = some (pc, instr)) :
    ∃ block compactSize,
      block ∈ artifact.blocks ∧
        block.sourcePc = pc ∧ block.sourceInstr = instr ∧
          sourceInstrSizeAt? artifact.pinnedPushPcs artifact.branchWidth
            block.sourcePc block.sourceInstr =
            some compactSize ∧
          emitSourceBlock? artifact.pinnedPushPcs artifact.branchWidth
            block.sourcePc block.compactPc artifact.labels block.sourceInstr =
              some block.code := by
  have hBlocks := compile?_blocksValid hCompile
  obtain ⟨block, hMem, hBlockPc, hInstr⟩ :=
    hBlocks.block_of_instrAtPc hAt
  obtain ⟨compactSize, hSize, hCode⟩ :=
    hBlocks.block_emit_of_mem hMem
  exact
    ⟨block, compactSize, hMem, hBlockPc, hInstr, hSize, hCode⟩

theorem compile?_initial_boundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    BoundaryPair artifact.blocks artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code) 0 0 := by
  have hArtifact := compile?_valid hCompile
  have hBoundary := (compile?_blocksValid hCompile).initial_boundary
  rw [hArtifact.blockCode] at hBoundary
  exact hBoundary

theorem compile?_physical_labelPc_of_lookup
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {label : Label} {compactPc : Nat}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hLookup : lookupLabel? artifact.labels label = some compactPc) :
    ∃ sourcePc, artifact.physicalSource.labelPc label = some sourcePc := by
  have hLayout := (compile?_valid hCompile).layout
  unfold layout? at hLayout
  have hNames := layoutRev?_names hLayout
  have hMem := lookupLabel?_name_mem hLookup
  rw [hNames] at hMem
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at hMem
  exact Assembly.Program.labelPc_exists_of_mem_labels
    artifact.physicalSource hMem

theorem compile?_label_boundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {label : Label} {sourceDest compactDest : Nat}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hSource : artifact.physicalSource.labelPc label = some sourceDest)
    (hCompact : lookupLabel? artifact.labels label = some compactDest) :
    BoundaryPair artifact.blocks artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      sourceDest compactDest := by
  have hArtifact := compile?_valid hCompile
  have hBlocks := compile?_blocksValid hCompile
  have hAt := Assembly.Program.instrAtPc_of_labelPc hSource
  obtain ⟨block, hMem, hBlockPc, hInstr⟩ :=
    hBlocks.block_of_instrAtPc hAt
  have hLabel :=
    hArtifact.labelsConsistent block hMem label hInstr
  rw [hCompact] at hLabel
  have hCompactPc : compactDest = block.compactPc :=
    Option.some.inj hLabel
  exact Or.inl ⟨block, hMem, hBlockPc, hCompactPc.symm⟩

theorem compile?_source_openStepResult_eq_block
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {block : SourceBlock} {state : EVMState}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.sourcePc) :
    Assembly.InteractionSemantics.Source.openStepResult
        artifact.physicalSource state =
      Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource block.sourcePc block.sourceInstr state := by
  have hArtifact := compile?_valid hCompile
  have hBlocks := compile?_blocksValid hCompile
  obtain ⟨pre, post, hSource, hBlockPc⟩ :=
    hBlocks.decompose_of_block_mem hBlock
  have hWholeFits := hArtifact.physicalSourcePCFits
  rw [hSource] at hWholeFits ⊢
  have hPreFits :=
    (Assembly.Program.PCFitsFrom.of_append
      (pre := pre) (code := block.sourceInstr :: post) (post := [])
      (by simpa using hWholeFits)).start
  apply Assembly.InteractionPreservation.source_openStepResult_at_boundary
    hPreFits
  simpa [Assembly.Program.pcAfter, hBlockPc] using hPc

theorem compile?_preparation_source_openStepResult_eq_block
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {block : PreparationBlock} {state : EVMState}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.sourcePc) :
    Assembly.InteractionSemantics.Source.openStepResult source state =
      Assembly.InteractionSemantics.Source.openStepAtResult
        source block.sourcePc block.sourceInstr state := by
  have hArtifact := compile?_valid hCompile
  have hPreparation := compile?_preparationBlocksValid hCompile
  obtain ⟨pre, post, hSource, hBlockPc⟩ :=
    hPreparation.source_decompose_of_block_mem hBlock
  have hWholeFits := hArtifact.sourcePCFits
  rw [hSource] at hWholeFits ⊢
  have hPreFits :=
    (Assembly.Program.PCFitsFrom.of_append
      (pre := pre) (code := block.sourceInstr :: post) (post := [])
      (by simpa using hWholeFits)).start
  apply Assembly.InteractionPreservation.source_openStepResult_at_boundary
    hPreFits
  simpa [Assembly.Program.pcAfter, hBlockPc] using hPc

theorem compile?_preparation_target_openStepResult_eq_block
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {block : PreparationBlock} {state : EVMState}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.preparedPc) :
    Assembly.InteractionSemantics.Source.openStepResult
        artifact.physicalSource state =
      Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource block.preparedPc block.sourceInstr state := by
  have hArtifact := compile?_valid hCompile
  have hPreparation := compile?_preparationBlocksValid hCompile
  obtain ⟨pre, post, hPrepared, hBlockPc⟩ :=
    hPreparation.prepared_decompose_of_keep hBlock hKeep
  have hWholeFits := hArtifact.physicalSourcePCFits
  rw [hPrepared] at hWholeFits ⊢
  have hPreFits :=
    (Assembly.Program.PCFitsFrom.of_append
      (pre := pre) (code := block.sourceInstr :: post) (post := [])
      (by simpa using hWholeFits)).start
  apply Assembly.InteractionPreservation.source_openStepResult_at_boundary
    hPreFits
  simpa [Assembly.Program.pcAfter, hBlockPc] using hPc

def StepResultRuntimeRel : StepResult -> StepResult -> Prop
  | .running target, .running source => SameRuntimeData target source
  | .halted target, .halted source =>
      target.kind = source.kind ∧
        SameRuntimeData target.state source.state ∧
          target.output = source.output
  | _, _ => False

abbrev RuntimeOutcomeRel :
    Except EVMException StepResult -> Except EVMException StepResult -> Prop :=
  Simulation.Interaction.ExceptRel
    (fun targetError sourceError => targetError = sourceError)
    StepResultRuntimeRel

def PreparationStateRel (sourceProgram : Assembly.Program)
    (artifact : Artifact) (target source : EVMState) : Prop :=
  ∃ sourcePc preparedPc,
    PreparationBoundaryPair artifact.preparation sourceProgram.byteLength
        artifact.physicalSource.byteLength sourcePc preparedPc ∧
      source.pc = EvmYul.UInt256.ofNat sourcePc ∧
      target.pc = EvmYul.UInt256.ofNat preparedPc ∧
      SameRuntimeData target source

theorem PreparationStateRel.active_of_terminal_succ
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {target source : EVMState} {fuel : Nat}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBoundary : PreparationStateRel sourceProgram artifact target source)
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram (fuel + 1) source)) :
    ∃ block,
      block ∈ artifact.preparation ∧
        source.pc = EvmYul.UInt256.ofNat block.sourcePc ∧
          target.pc = EvmYul.UInt256.ofNat block.preparedPc ∧
            SameRuntimeData target source := by
  rcases hBoundary with
    ⟨sourcePc, preparedPc, hPair, hSourcePc, hTargetPc, hRel⟩
  rcases hPair with hBlock | hEnd
  · rcases hBlock with ⟨block, hMem, hBlockSource, hBlockPrepared⟩
    exact
      ⟨block, hMem, by simpa [hBlockSource] using hSourcePc,
        by simpa [hBlockPrepared] using hTargetPc, hRel⟩
  · rcases hEnd with ⟨hSourceEnd, _hPreparedEnd⟩
    have hArtifact := compile?_valid hCompile
    have hToNat : source.pc.toNat = sourceProgram.byteLength := by
      rw [hSourcePc, hSourceEnd]
      exact hArtifact.sourcePCFits
    have hStep :
        Assembly.InteractionSemantics.Source.openStepResult sourceProgram source =
          .done (.error EvmYul.EVM.ExecutionException.InvalidInstruction) := by
      unfold Assembly.InteractionSemantics.Source.openStepResult
        Assembly.Source.stepResultWith
      rw [hToNat, instrAtPc_end_eq_none]
      rfl
    rw [Assembly.InteractionSemantics.Source.openRunNResult_succ] at hTerminal
    have hPrefix := Simulation.Interaction.AllDone.bind_inv hTerminal
    rw [hStep] at hPrefix
    cases hPrefix with
    | done hDone => exact False.elim hDone

def PreparationStepResultRel (sourceProgram : Assembly.Program)
    (artifact : Artifact) : StepResult -> StepResult -> Prop
  | .running target, .running source =>
      PreparationStateRel sourceProgram artifact target source
  | .halted target, .halted source =>
      target.kind = source.kind ∧
        SameRuntimeData target.state source.state ∧
          target.output = source.output
  | _, _ => False

abbrev PreparationOutcomeRel (sourceProgram : Assembly.Program)
    (artifact : Artifact) :
    Except EVMException StepResult -> Except EVMException StepResult -> Prop :=
  Simulation.Interaction.ExceptRel
    (fun targetError sourceError => targetError = sourceError)
    (PreparationStepResultRel sourceProgram artifact)

def BoundaryStateRel (artifact : Artifact)
    (target source : EVMState) : Prop :=
  ∃ sourcePc compactPc,
    BoundaryPair artifact.blocks artifact.physicalSource.byteLength
        (Program.codeByteLength artifact.program.code) sourcePc compactPc ∧
      source.pc = EvmYul.UInt256.ofNat sourcePc ∧
      target.pc = EvmYul.UInt256.ofNat compactPc ∧
      SameRuntimeData target source

theorem BoundaryStateRel.active_of_terminal_succ
    {input : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {target source : EVMState} {fuel : Nat}
    (hCompile : compile? input pinnedPushPcs = some artifact)
    (hBoundary : BoundaryStateRel artifact target source)
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource (fuel + 1) source)) :
    ∃ block,
      block ∈ artifact.blocks ∧
        source.pc = EvmYul.UInt256.ofNat block.sourcePc ∧
          target.pc = EvmYul.UInt256.ofNat block.compactPc ∧
            SameRuntimeData target source := by
  rcases hBoundary with
    ⟨sourcePc, compactPc, hPair, hSourcePc, hTargetPc, hRel⟩
  rcases hPair with hBlock | hEnd
  · rcases hBlock with ⟨block, hMem, hBlockSource, hBlockCompact⟩
    exact
      ⟨block, hMem, by simpa [hBlockSource] using hSourcePc,
        by simpa [hBlockCompact] using hTargetPc, hRel⟩
  · rcases hEnd with ⟨hSourceEnd, _hCompactEnd⟩
    have hArtifact := compile?_valid hCompile
    have hToNat : source.pc.toNat = artifact.physicalSource.byteLength := by
      rw [hSourcePc, hSourceEnd]
      exact hArtifact.physicalSourcePCFits
    have hStep :
        Assembly.InteractionSemantics.Source.openStepResult
            artifact.physicalSource source =
          .done (.error EvmYul.EVM.ExecutionException.InvalidInstruction) := by
      unfold Assembly.InteractionSemantics.Source.openStepResult
        Assembly.Source.stepResultWith
      rw [hToNat, instrAtPc_end_eq_none]
      rfl
    rw [Assembly.InteractionSemantics.Source.openRunNResult_succ] at hTerminal
    have hPrefix := Simulation.Interaction.AllDone.bind_inv hTerminal
    rw [hStep] at hPrefix
    cases hPrefix with
    | done hDone => exact False.elim hDone

def BoundaryStepResultRel (artifact : Artifact) :
    StepResult -> StepResult -> Prop
  | .running target, .running source => BoundaryStateRel artifact target source
  | .halted target, .halted source =>
      target.kind = source.kind ∧
        SameRuntimeData target.state source.state ∧
          target.output = source.output
  | _, _ => False

abbrev BoundaryOutcomeRel (artifact : Artifact) :
    Except EVMException StepResult -> Except EVMException StepResult -> Prop :=
  Simulation.Interaction.ExceptRel
    (fun targetError sourceError => targetError = sourceError)
    (BoundaryStepResultRel artifact)

def RunningAt (pc : Word) : Except EVMException StepResult -> Prop
  | .ok (.running state) => state.pc = pc
  | _ => True

theorem runtimeRel_to_preparationRel
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {targetRun sourceRun : Assembly.InteractionSemantics.OpenStepResult}
    {sourcePc preparedPc : Nat}
    (hBoundary : PreparationBoundaryPair artifact.preparation
      sourceProgram.byteLength artifact.physicalSource.byteLength
      sourcePc preparedPc)
    (hRel : Simulation.Interaction.Rel RuntimeOutcomeRel targetRun sourceRun)
    (hTargetPc : Simulation.Interaction.AllDone
      (RunningAt (EvmYul.UInt256.ofNat preparedPc)) targetRun)
    (hSourcePc : Simulation.Interaction.AllDone
      (RunningAt (EvmYul.UInt256.ofNat sourcePc)) sourceRun) :
    Simulation.Interaction.Rel
      (PreparationOutcomeRel sourceProgram artifact) targetRun sourceRun := by
  have hTarget := Simulation.Interaction.Rel.strengthen_left hRel hTargetPc
  have hBoth :=
    Simulation.Interaction.Rel.strengthen_right hTarget hSourcePc
  apply Simulation.Interaction.Rel.mono hBoth
  intro targetDone sourceDone hDone
  rcases hDone with ⟨⟨hRuntime, hTargetAt⟩, hSourceAt⟩
  cases hRuntime with
  | error hError => exact .error hError
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult with
      | running target =>
          cases sourceResult with
          | running source =>
              apply Simulation.Interaction.ExceptRel.ok
              change target.pc = EvmYul.UInt256.ofNat preparedPc at hTargetAt
              change source.pc = EvmYul.UInt256.ofNat sourcePc at hSourceAt
              exact
                ⟨sourcePc, preparedPc, hBoundary,
                  hSourceAt, hTargetAt, hResult⟩
          | halted source => simp [StepResultRuntimeRel] at hResult
      | halted target =>
          cases sourceResult with
          | running source => simp [StepResultRuntimeRel] at hResult
          | halted source => exact .ok hResult

theorem runtimeRel_to_boundaryRel
    {artifact : Artifact} {targetRun sourceRun :
      Assembly.InteractionSemantics.OpenStepResult}
    {sourcePc compactPc : Nat}
    (hBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code) sourcePc compactPc)
    (hRel : Simulation.Interaction.Rel RuntimeOutcomeRel
      targetRun sourceRun)
    (hTargetPc : Simulation.Interaction.AllDone
      (RunningAt (EvmYul.UInt256.ofNat compactPc)) targetRun)
    (hSourcePc : Simulation.Interaction.AllDone
      (RunningAt (EvmYul.UInt256.ofNat sourcePc)) sourceRun) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      targetRun sourceRun := by
  have hTarget := Simulation.Interaction.Rel.strengthen_left hRel hTargetPc
  have hBoth :=
    Simulation.Interaction.Rel.strengthen_right hTarget hSourcePc
  apply Simulation.Interaction.Rel.mono hBoth
  intro targetDone sourceDone hDone
  rcases hDone with ⟨⟨hRuntime, hTargetAt⟩, hSourceAt⟩
  cases hRuntime with
  | error hError => exact .error hError
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult with
      | running target =>
          cases sourceResult with
          | running source =>
              apply Simulation.Interaction.ExceptRel.ok
              change target.pc = EvmYul.UInt256.ofNat compactPc at hTargetAt
              change source.pc = EvmYul.UInt256.ofNat sourcePc at hSourceAt
              exact
                ⟨sourcePc, compactPc, hBoundary,
                  hSourceAt, hTargetAt, hResult⟩
          | halted source =>
              simp [StepResultRuntimeRel] at hResult
      | halted target =>
          cases sourceResult with
          | running source =>
              simp [StepResultRuntimeRel] at hResult
          | halted source =>
              apply Simulation.Interaction.ExceptRel.ok
              exact hResult

namespace Instr

def toLogical : Instr -> TargetInstr
  | .push _ value => .push32 value
  | .jump => .jump
  | .jumpi => .jumpi
  | .jumpdest => .jumpdest
  | .prim op => .prim op

def haltKind? : Instr -> Option HaltKind
  | .prim op => op.haltKind?
  | _ => none

def openStep : Instr -> EVMState -> Assembly.InteractionSemantics.OpenStep
  | .push width value, state =>
      Assembly.InteractionSemantics.Target.openStepPush
        width value state
  | .jump, state =>
      Assembly.InteractionSemantics.Target.openStepInstr .jump state
  | .jumpi, state =>
      Assembly.InteractionSemantics.Target.openStepInstr .jumpi state
  | .jumpdest, state =>
      Assembly.InteractionSemantics.Target.openStepInstr .jumpdest state
  | .prim op, state =>
      Assembly.InteractionSemantics.Target.openStepInstr (.prim op) state

def openStepResult (instr : Instr) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult := do
  let state' <- instr.openStep state
  match instr.haltKind? with
  | some kind =>
      pure (.halted
        { kind := kind
          state := state'
          output := kind.output state' })
  | none => pure (.running state')

end Instr

theorem haltOutput_eq_of_sameRuntimeData
    {target source : EVMState} (kind : HaltKind)
    (hRel : SameRuntimeData target source) :
    kind.output target = kind.output source := by
  have hShared := SameRuntimeData.shared_eq hRel
  cases kind <;> simp [HaltKind.output, hShared]

namespace Instr

theorem toLogical_haltKind? (instr : Instr) :
    instr.toLogical.haltKind? = instr.haltKind? := by
  cases instr <;> rfl

/-- A compact instruction and its logical PUSH32-era counterpart expose the
same open interaction and runtime data. Their physical PCs may differ. -/
theorem openStep_runtimeRel
    {instr : Instr} {target source : EVMState}
    (hIndependent : instr.PCIndependent)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel
      Assembly.InteractionPreservation.PrimOp.RuntimeStateRel
      (instr.openStep target)
      (Assembly.InteractionSemantics.Target.openStepInstr
        instr.toLogical source) := by
  cases instr with
  | push width value =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        SameRuntimeData.replaceStackAndIncrPC_of_deltas hRel
          (congrArg (fun stack => stack.push value)
            (SameRuntimeData.stack_eq hRel))
  | jump =>
      change Simulation.Interaction.Rel _
        (Assembly.InteractionSemantics.Target.openStepInstr .jump target)
        (Assembly.InteractionSemantics.Target.openStepInstr .jump source)
      unfold Assembly.InteractionSemantics.Target.openStepInstr
        Assembly.Target.stepInstrWith
      have hStack := SameRuntimeData.stack_eq hRel
      rw [hStack]
      cases hPop : source.stack.pop with
      | none => exact .done (.error rfl)
      | some pair =>
          rcases pair with ⟨rest, dest⟩
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact
            SameRuntimeData.with_pc_right dest
              (SameRuntimeData.with_pc_left dest
                (SameRuntimeData.replaceStack
                  (targetStack := rest) (sourceStack := rest) hRel rfl))
  | jumpi =>
      change Simulation.Interaction.Rel _
        (Assembly.InteractionSemantics.Target.openStepInstr .jumpi target)
        (Assembly.InteractionSemantics.Target.openStepInstr .jumpi source)
      unfold Assembly.InteractionSemantics.Target.openStepInstr
        Assembly.Target.stepInstrWith
      have hStack := SameRuntimeData.stack_eq hRel
      rw [hStack]
      cases hPop : source.stack.pop2 with
      | none => exact .done (.error rfl)
      | some values =>
          rcases values with ⟨rest, dest, cond⟩
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact
            SameRuntimeData.with_pc_right
              (if cond != EvmYul.UInt256.ofNat 0 then
                dest else source.pc + EvmYul.UInt256.ofNat 1)
              (SameRuntimeData.with_pc_left
                (if cond != EvmYul.UInt256.ofNat 0 then
                  dest else target.pc + EvmYul.UInt256.ofNat 1)
                (SameRuntimeData.replaceStack
                  (targetStack := rest) (sourceStack := rest) hRel rfl))
  | jumpdest =>
      change Simulation.Interaction.Rel _
        (Assembly.InteractionSemantics.Target.openStepInstr .jumpdest target)
        (Assembly.InteractionSemantics.Target.openStepInstr .jumpdest source)
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        SameRuntimeData.incrPC_right
          (SameRuntimeData.incrPC_left hRel)
  | prim op =>
      have hNoPc : op ≠ .pc := by
        intro hOp
        subst op
        simpa [PCIndependent] using hIndependent
      exact
        Assembly.InteractionPreservation.PrimOp.openStep_runtimeRel_of_ne_pc
          hNoPc hRel

theorem openStepResult_runtimeRel
    {instr : Instr} {target source : EVMState}
    (hIndependent : instr.PCIndependent)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (instr.openStepResult target)
      (Assembly.InteractionSemantics.Target.openStepInstrResult
        instr.toLogical source) := by
  unfold openStepResult
    Assembly.InteractionSemantics.Target.openStepInstrResult
    Assembly.Target.stepInstrResultWith
  rw [toLogical_haltKind?]
  apply Simulation.Interaction.Rel.bind
    (openStep_runtimeRel hIndependent hRel)
  intro targetFinal sourceFinal hFinal
  cases hKind : instr.haltKind? with
  | none =>
      exact .done (.ok hFinal)
  | some kind =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        ⟨rfl, hFinal,
          haltOutput_eq_of_sameRuntimeData kind hFinal⟩

theorem openStepResult_runningAt_next
    {instr : Instr} {state : EVMState}
    (hSequential : instr.Sequential) :
    Simulation.Interaction.AllDone
      (RunningAt
        (state.pc + EvmYul.UInt256.ofNat instr.byteSize))
      (instr.openStepResult state) := by
  cases instr with
  | push width value =>
      exact .done rfl
  | jump => cases hSequential
  | jumpi => cases hSequential
  | jumpdest =>
      exact .done rfl
  | prim op =>
      by_cases hArity : ∃ arity, op.stackArity? = some arity
      · rcases hArity with ⟨⟨input, output⟩, hArity⟩
        have hAdvances :=
          Assembly.InteractionPreservation.PrimOp.openStep_advancesPC
            (state := state) hArity
        unfold openStepResult openStep
        apply Simulation.Interaction.AllDone.bind hAdvances
        · intro err _hError
          trivial
        · intro final hFinal
          have hKind : (Instr.prim op).haltKind? = none := by
            cases op <;>
              simp [Assembly.PrimOp.stackArity?,
                Assembly.PrimOp.haltKind?, Instr.haltKind?]
                at hArity ⊢
          rw [hKind]
          apply Simulation.Interaction.AllDone.done
          change final.pc = state.pc + EvmYul.UInt256.ofNat 1
          exact hFinal
      · by_cases hTerminal : ∃ kind, op.haltKind? = some kind
        · rcases hTerminal with ⟨kind, hKind⟩
          unfold openStepResult openStep
          apply Simulation.Interaction.AllDone.bind
            (Simulation.Interaction.AllDone.trivial
              (Assembly.InteractionSemantics.PrimOp.openStep op state))
          · intro err _hError
            trivial
          · intro final _hFinal
            have hCompactKind : (Instr.prim op).haltKind? = some kind := by
              simpa [Instr.haltKind?] using hKind
            rw [hCompactKind]
            exact .done trivial
        · have hInvalid : op = .invalid := by
            cases op <;>
              simp [Assembly.PrimOp.stackArity?, Assembly.PrimOp.haltKind?]
                at hArity hTerminal ⊢
          subst op
          change Simulation.Interaction.AllDone _
            (.done (.error EvmYul.EVM.ExecutionException.InvalidInstruction))
          exact .done trivial

end Instr

namespace InteractionSemantics

inductive SimpleSourceInstrRel : Assembly.Instr -> Instr -> Prop
  | label (name : Label) : SimpleSourceInstrRel (.label name) .jumpdest
  | prim (op : PrimOp) : SimpleSourceInstrRel (.prim op) (.prim op)
  | push (width : Nat) (value : Word) :
      SimpleSourceInstrRel (.push value) (.push width value)

theorem SimpleSourceInstrRel.openStepResult_eq
    {sourceInstr : Assembly.Instr} {compactInstr : Instr}
    (hInstr : SimpleSourceInstrRel sourceInstr compactInstr)
    (program : Assembly.Program) (pc : Nat) (state : EVMState) :
    Assembly.InteractionSemantics.Source.openStepAtResult
        program pc sourceInstr state =
      Assembly.InteractionSemantics.Target.openStepInstrResult
        compactInstr.toLogical state := by
  cases hInstr <;> rfl

theorem SimpleSourceInstrRel.source_runningAt_next
    {sourceInstr : Assembly.Instr} {compactInstr : Instr}
    (hInstr : SimpleSourceInstrRel sourceInstr compactInstr)
    (program : Assembly.Program) (pc : Nat) (state : EVMState) :
    Simulation.Interaction.AllDone
      (RunningAt
        (state.pc + EvmYul.UInt256.ofNat sourceInstr.byteSize))
      (Assembly.InteractionSemantics.Source.openStepAtResult
        program pc sourceInstr state) := by
  cases hInstr with
  | label name =>
      exact Instr.openStepResult_runningAt_next
        (instr := Instr.jumpdest) (state := state) trivial
  | prim op =>
      exact Instr.openStepResult_runningAt_next
        (instr := Instr.prim op) (state := state) trivial
  | push width value =>
      simpa [Assembly.Instr.byteSize, Instr.byteSize] using
        (Instr.openStepResult_runningAt_next
          (instr := Instr.push 32 value) (state := state) trivial)

theorem SimpleSourceInstrRel.compactSequential
    {sourceInstr : Assembly.Instr} {compactInstr : Instr}
    (hInstr : SimpleSourceInstrRel sourceInstr compactInstr) :
    compactInstr.Sequential := by
  cases hInstr <;> trivial

inductive PreparationSimpleInstr : Assembly.Instr -> Prop
  | label (name : Label) : PreparationSimpleInstr (.label name)
  | prim (op : PrimOp) (hNoPc : op ≠ .pc) :
      PreparationSimpleInstr (.prim op)
  | push (value : Word) : PreparationSimpleInstr (.push value)

theorem PreparationSimpleInstr.openStepAtResult_runtimeRel
    {instr : Assembly.Instr} (hSimple : PreparationSimpleInstr instr)
    (targetProgram sourceProgram : Assembly.Program)
    (targetPc sourcePc : Nat) {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (Assembly.InteractionSemantics.Source.openStepAtResult
        targetProgram targetPc instr target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram sourcePc instr source) := by
  cases hSimple with
  | label name =>
      rw [(SimpleSourceInstrRel.label name).openStepResult_eq
        targetProgram targetPc target]
      rw [(SimpleSourceInstrRel.label name).openStepResult_eq
        sourceProgram sourcePc source]
      simpa [Instr.openStepResult, Instr.openStep, Instr.haltKind?] using
        (Instr.openStepResult_runtimeRel
          (instr := Instr.jumpdest) (target := target) (source := source)
          trivial hRel)
  | prim op hNoPc =>
      rw [(SimpleSourceInstrRel.prim op).openStepResult_eq
        targetProgram targetPc target]
      rw [(SimpleSourceInstrRel.prim op).openStepResult_eq
        sourceProgram sourcePc source]
      have hIndependent : (Instr.prim op).PCIndependent := by
        cases op <;> simp [Instr.PCIndependent] at hNoPc ⊢
      simpa [Instr.openStepResult, Instr.openStep, Instr.haltKind?] using
        (Instr.openStepResult_runtimeRel
          (instr := Instr.prim op) (target := target) (source := source)
          hIndependent hRel)
  | push value =>
      rw [(SimpleSourceInstrRel.push 32 value).openStepResult_eq
        targetProgram targetPc target]
      rw [(SimpleSourceInstrRel.push 32 value).openStepResult_eq
        sourceProgram sourcePc source]
      simpa [Instr.openStepResult, Instr.openStep, Instr.haltKind?] using
        (Instr.openStepResult_runtimeRel
          (instr := Instr.push 32 value) (target := target) (source := source)
          trivial hRel)

theorem PreparationSimpleInstr.source_runningAt_next
    {instr : Assembly.Instr} (hSimple : PreparationSimpleInstr instr)
    (program : Assembly.Program) (pc : Nat) (state : EVMState) :
    Simulation.Interaction.AllDone
      (RunningAt (state.pc + EvmYul.UInt256.ofNat instr.byteSize))
      (Assembly.InteractionSemantics.Source.openStepAtResult
        program pc instr state) := by
  cases hSimple with
  | label name =>
      exact (SimpleSourceInstrRel.label name).source_runningAt_next
        program pc state
  | prim op hNoPc =>
      exact (SimpleSourceInstrRel.prim op).source_runningAt_next
        program pc state
  | push value =>
      exact (SimpleSourceInstrRel.push 32 value).source_runningAt_next
        program pc state

theorem compile?_preparation_simple_block_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : PreparationBlock} {target source : EVMState}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hSimple : PreparationSimpleInstr block.sourceInstr)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (PreparationOutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hPreparation := compile?_preparationBlocksValid hCompile
  have hNext := hPreparation.next_boundary hBlock
  have hTargetStep :=
    compile?_preparation_target_openStepResult_eq_block
      hCompile hBlock hKeep hTargetPc
  rw [Assembly.InteractionSemantics.Source.openRunNResult_one, hTargetStep]
  apply runtimeRel_to_preparationRel (by simpa using hNext)
    (hSimple.openStepAtResult_runtimeRel artifact.physicalSource sourceProgram
      block.preparedPc block.sourcePc hRel)
  · simpa [PreparationBlock.nextPreparedPc, hKeep, hTargetPc,
      UInt256_ofNat_add] using
      hSimple.source_runningAt_next artifact.physicalSource
        block.preparedPc target
  · simpa [hSourcePc, UInt256_ofNat_add] using
      hSimple.source_runningAt_next sourceProgram block.sourcePc source

theorem compile?_preparation_skip_label_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : PreparationBlock} {name : Label}
    {target source : EVMState}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .label name)
    (hSkip : block.action = .skip)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (PreparationOutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 0 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hPreparation := compile?_preparationBlocksValid hCompile
  have hNext := hPreparation.next_boundary hBlock
  rw [hInstr] at hNext ⊢
  rw [Assembly.InteractionSemantics.Source.openRunNResult_zero]
  apply runtimeRel_to_preparationRel
    (by simpa [PreparationBlock.nextPreparedPc, hSkip] using hNext)
  · rw [(SimpleSourceInstrRel.label name).openStepResult_eq
      sourceProgram block.sourcePc source]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact SameRuntimeData.with_pc_right
      (source.pc + EvmYul.UInt256.ofNat 1) hRel
  · exact .done hTargetPc
  · simpa [hSourcePc, UInt256_ofNat_add,
      Assembly.Instr.byteSize] using
      (SimpleSourceInstrRel.label name).source_runningAt_next
        sourceProgram block.sourcePc source

theorem compile?_preparation_skip_jump_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : PreparationBlock} {label : Label}
    {target source : EVMState}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .jump label)
    (hSkip : block.action = .skip)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (PreparationOutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 0 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hSafe := compile?_preparationSafe hCompile block hBlock
  unfold PreparationBlockSafe at hSafe
  rw [hSkip, hInstr] at hSafe
  change ∃ sourceDest,
    sourceProgram.labelPc label = some sourceDest ∧
      preparationTargetPc? artifact.preparation sourceProgram.byteLength
        artifact.physicalSource.byteLength sourceDest =
          some block.preparedPc at hSafe
  obtain ⟨sourceDest, hSourceDest, hLookup⟩ := hSafe
  have hBoundary := preparationBoundaryPair_of_targetPc? hLookup
  rw [hInstr, Assembly.InteractionSemantics.Source.openRunNResult_zero]
  apply runtimeRel_to_preparationRel hBoundary
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done (.ok
      (SameRuntimeData.with_pc_right
        (EvmYul.UInt256.ofNat sourceDest) hRel))
  · exact .done hTargetPc
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done rfl

theorem compile?_preparation_keep_jump_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : PreparationBlock} {label : Label}
    {target source : EVMState}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .jump label)
    (hKeep : block.action = .keep)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (PreparationOutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hSafe := compile?_preparationSafe hCompile block hBlock
  unfold PreparationBlockSafe at hSafe
  rw [hKeep, hInstr] at hSafe
  change ∃ sourceDest preparedDest,
    sourceProgram.labelPc label = some sourceDest ∧
      artifact.physicalSource.labelPc label = some preparedDest ∧
        preparationTargetPc? artifact.preparation sourceProgram.byteLength
          artifact.physicalSource.byteLength sourceDest =
            some preparedDest at hSafe
  obtain ⟨sourceDest, preparedDest, hSourceDest, hPreparedDest, hLookup⟩ :=
    hSafe
  have hBoundary := preparationBoundaryPair_of_targetPc? hLookup
  have hTargetStep :=
    compile?_preparation_target_openStepResult_eq_block
      hCompile hBlock hKeep hTargetPc
  rw [hInstr] at hTargetStep
  rw [hInstr, Assembly.InteractionSemantics.Source.openRunNResult_one,
    hTargetStep]
  apply runtimeRel_to_preparationRel hBoundary
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp [hSourceDest, hPreparedDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done (Simulation.Interaction.ExceptRel.ok
      (SameRuntimeData.with_pc_right (EvmYul.UInt256.ofNat sourceDest)
        (SameRuntimeData.with_pc_left
          (EvmYul.UInt256.ofNat preparedDest) hRel)))
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp [hPreparedDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done rfl
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done rfl

theorem compile?_preparation_keep_jumpi_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : PreparationBlock} {label : Label}
    {target source : EVMState}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .jumpi label)
    (hKeep : block.action = .keep)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (PreparationOutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hSafe := compile?_preparationSafe hCompile block hBlock
  unfold PreparationBlockSafe at hSafe
  rw [hKeep, hInstr] at hSafe
  change ∃ sourceDest preparedDest,
    sourceProgram.labelPc label = some sourceDest ∧
      artifact.physicalSource.labelPc label = some preparedDest ∧
        preparationTargetPc? artifact.preparation sourceProgram.byteLength
          artifact.physicalSource.byteLength sourceDest =
            some preparedDest at hSafe
  obtain ⟨sourceDest, preparedDest, hSourceDest, hPreparedDest, hLookup⟩ :=
    hSafe
  have hTakenBoundary := preparationBoundaryPair_of_targetPc? hLookup
  have hPreparation := compile?_preparationBlocksValid hCompile
  have hNextBoundary := hPreparation.next_boundary hBlock
  have hTargetStep :=
    compile?_preparation_target_openStepResult_eq_block
      hCompile hBlock hKeep hTargetPc
  rw [hInstr] at hTargetStep hNextBoundary ⊢
  rw [Assembly.InteractionSemantics.Source.openRunNResult_one, hTargetStep]
  have hStack := SameRuntimeData.stack_eq hRel
  have hRuntime : Simulation.Interaction.Rel RuntimeOutcomeRel
      (Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource block.preparedPc (.jumpi label) target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc (.jumpi label) source) := by
    unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp only [hSourceDest, hPreparedDest, Option.elim_some,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind_done_ok]
    rw [hStack]
    cases hSourceStack : source.stack with
    | nil =>
        simp [hSourceStack, EvmYul.Stack.pop]
        exact .done (.error rfl)
    | cons cond stack =>
        simp [hSourceStack, EvmYul.Stack.pop]
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact
          SameRuntimeData.with_pc_right
            (if cond != EvmYul.UInt256.ofNat 0 then
              EvmYul.UInt256.ofNat sourceDest
            else Assembly.Source.jumpiFallthroughPc source)
            (SameRuntimeData.with_pc_left
              (if cond != EvmYul.UInt256.ofNat 0 then
                EvmYul.UInt256.ofNat preparedDest
              else Assembly.Source.jumpiFallthroughPc target)
              (SameRuntimeData.replaceStack
                (targetStack := stack) (sourceStack := stack) hRel rfl))
  cases hSourceStack : source.stack with
  | nil =>
      apply runtimeRel_to_preparationRel
        (by simpa [PreparationBlock.nextPreparedPc, hKeep, hInstr]
          using hNextBoundary)
        hRuntime
      · unfold Assembly.InteractionSemantics.Source.openStepAtResult
          Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
        simp [hPreparedDest, hStack, hSourceStack,
          Assembly.Instr.haltKind?, EvmYul.Stack.pop]
        exact .done trivial
      · unfold Assembly.InteractionSemantics.Source.openStepAtResult
          Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
        simp [hSourceDest, hSourceStack,
          Assembly.Instr.haltKind?, EvmYul.Stack.pop]
        exact .done trivial
  | cons cond stack =>
      by_cases hCond : (cond != EvmYul.UInt256.ofNat 0) = true
      · apply runtimeRel_to_preparationRel hTakenBoundary hRuntime
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
          simp [hPreparedDest, hStack, hSourceStack, hCond,
            Assembly.Instr.haltKind?, EvmYul.Stack.pop]
          exact .done (by simp [RunningAt, hCond])
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
          simp [hSourceDest, hSourceStack, hCond,
            Assembly.Instr.haltKind?, EvmYul.Stack.pop]
          exact .done (by simp [RunningAt, hCond])
      · apply runtimeRel_to_preparationRel
          (by simpa [PreparationBlock.nextPreparedPc, hKeep, hInstr]
            using hNextBoundary)
          hRuntime
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
          simp [hPreparedDest, hStack, hSourceStack, hCond,
            Assembly.Source.jumpiFallthroughPc, Assembly.Instr.byteSize,
            Assembly.Instr.jumpSize, Assembly.Instr.push32Size,
            Assembly.Instr.haltKind?, EvmYul.Stack.pop, hTargetPc,
            UInt256_ofNat_add, UInt256_add_assoc, Nat.add_assoc]
          exact .done (by simp [RunningAt, hCond])
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
          simp [hSourceDest, hSourceStack, hCond,
            Assembly.Source.jumpiFallthroughPc, Assembly.Instr.byteSize,
            Assembly.Instr.jumpSize, Assembly.Instr.push32Size,
            Assembly.Instr.haltKind?, EvmYul.Stack.pop, hSourcePc,
            UInt256_ofNat_add, UInt256_add_assoc, Nat.add_assoc]
          exact .done (by simp [RunningAt, hCond])

theorem compile?_preparationBlock_open_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : PreparationBlock} {target source : EVMState}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : SameRuntimeData target source) :
    ∃ targetFuel,
      targetFuel <= 1 ∧
        Simulation.Interaction.Rel
          (PreparationOutcomeRel sourceProgram artifact)
          (Assembly.InteractionSemantics.Source.openRunNResult
            artifact.physicalSource targetFuel target)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            sourceProgram block.sourcePc block.sourceInstr source) := by
  cases hAction : block.action with
  | keep =>
      cases hInstr : block.sourceInstr with
      | label name =>
          have hSimple : PreparationSimpleInstr block.sourceInstr :=
            hInstr.symm ▸ PreparationSimpleInstr.label name
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_simple_block_rel hCompile hBlock hAction
              hSimple hTargetPc hSourcePc hRel)
      | prim op =>
          have hNoPc : op ≠ .pc := by
            intro hPc
            subst op
            have hSafe := compile?_preparationSafe hCompile block hBlock
            unfold PreparationBlockSafe at hSafe
            rw [hAction, hInstr] at hSafe
            exact hSafe
          have hSimple : PreparationSimpleInstr block.sourceInstr :=
            hInstr.symm ▸ PreparationSimpleInstr.prim op hNoPc
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_simple_block_rel hCompile hBlock hAction
              hSimple hTargetPc hSourcePc hRel)
      | push value =>
          have hSimple : PreparationSimpleInstr block.sourceInstr :=
            hInstr.symm ▸ PreparationSimpleInstr.push value
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_simple_block_rel hCompile hBlock hAction
              hSimple hTargetPc hSourcePc hRel)
      | pushLabel label =>
          have hSafe := compile?_preparationSafe hCompile block hBlock
          unfold PreparationBlockSafe at hSafe
          rw [hAction, hInstr] at hSafe
          exact False.elim hSafe
      | jump label =>
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_keep_jump_rel hCompile hBlock hInstr
              hAction hTargetPc hRel)
      | jumpi label =>
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_keep_jumpi_rel hCompile hBlock hInstr
              hAction hTargetPc hSourcePc hRel)
      | jumpDynamic =>
          have hSafe := compile?_preparationSafe hCompile block hBlock
          unfold PreparationBlockSafe at hSafe
          rw [hAction, hInstr] at hSafe
          exact False.elim hSafe
  | skip =>
      cases hInstr : block.sourceInstr with
      | label name =>
          refine ⟨0, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_skip_label_rel hCompile hBlock hInstr
              hAction hTargetPc hSourcePc hRel)
      | jump label =>
          refine ⟨0, by omega, ?_⟩
          simpa [hInstr] using
            (compile?_preparation_skip_jump_rel hCompile hBlock hInstr
              hAction hTargetPc hRel)
      | prim op | push op | pushLabel op | jumpi op =>
          have hSafe := compile?_preparationSafe hCompile block hBlock
          unfold PreparationBlockSafe at hSafe
          rw [hAction, hInstr] at hSafe
          exact False.elim hSafe
      | jumpDynamic =>
          have hSafe := compile?_preparationSafe hCompile block hBlock
          unfold PreparationBlockSafe at hSafe
          rw [hAction, hInstr] at hSafe
          exact False.elim hSafe

theorem compile?_preparation_openRunNResult_terminal_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (fuel extra : Nat) {target source : EVMState}
    (hBoundary : PreparationStateRel sourceProgram artifact target source)
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source)) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource (fuel + extra) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source) := by
  induction fuel generalizing target source extra with
  | zero =>
      change Simulation.Interaction.AllDone
        Assembly.InteractionSemantics.Terminal
        (.done (.ok (.running source))) at hTerminal
      cases hTerminal with
      | done hDone => exact False.elim hDone
  | succ fuel ih =>
      have hTerminalSucc : Simulation.Interaction.AllDone
          Assembly.InteractionSemantics.Terminal
          (Assembly.InteractionSemantics.Source.openRunNResult
            sourceProgram (fuel + 1) source) := by
        simpa [Nat.succ_eq_add_one] using hTerminal
      obtain ⟨block, hBlock, hSourcePc, hTargetPc, hRuntime⟩ :=
        hBoundary.active_of_terminal_succ hCompile hTerminalSucc
      obtain ⟨stepFuel, hStepFuel, hStep⟩ :=
        compile?_preparationBlock_open_rel hCompile hBlock
          hTargetPc hSourcePc hRuntime
      have hSourceStep :=
        compile?_preparation_source_openStepResult_eq_block
          hCompile hBlock hSourcePc
      have hTerminalExpanded := hTerminalSucc
      rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
        hSourceStep] at hTerminalExpanded
      have hStepTerminal :=
        Simulation.Interaction.AllDone.bind_inv hTerminalExpanded
      have hStepStrong :=
        Simulation.Interaction.Rel.strengthen_right hStep hStepTerminal
      let remaining := fuel + (extra + (1 - stepFuel))
      have hFuel : Nat.succ fuel + extra = stepFuel + remaining := by
        dsimp [remaining]
        omega
      rw [hFuel,
        Assembly.InteractionSemantics.Source.openRunNResult_add]
      rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
        hSourceStep]
      apply Simulation.Interaction.Rel.bind_custom hStepStrong
      intro targetDone sourceDone hDone
      rcases hDone with ⟨hRelated, hContinuationTerminal⟩
      cases hRelated with
      | error hError => exact False.elim hContinuationTerminal
      | ok hResult =>
          rename_i targetResult sourceResult
          cases targetResult with
          | running targetMid =>
              cases sourceResult with
              | running sourceMid =>
                  change PreparationStateRel sourceProgram artifact
                    targetMid sourceMid at hResult
                  change Simulation.Interaction.AllDone
                    Assembly.InteractionSemantics.Terminal
                    (Assembly.InteractionSemantics.Source.openRunNResult
                      sourceProgram fuel sourceMid) at hContinuationTerminal
                  exact ih (extra + (1 - stepFuel)) hResult
                    hContinuationTerminal
              | halted sourceHalt =>
                  simp [PreparationStepResultRel] at hResult
          | halted targetHalt =>
              cases sourceResult with
              | running sourceMid =>
                  simp [PreparationStepResultRel] at hResult
              | halted sourceHalt =>
                  change targetHalt.kind = sourceHalt.kind ∧
                    SameRuntimeData targetHalt.state sourceHalt.state ∧
                      targetHalt.output = sourceHalt.output at hResult
                  exact .done (.ok hResult)

/-- Preparation preserves every finished branch. Unlike the terminal-only
theorem, this also handles source falloff at the preparation boundary by
matching the same `InvalidInstruction` in the prepared program. -/
theorem compile?_preparation_openRunNResult_finished_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (fuel extra : Nat) {target source : EVMState}
    (hBoundary : PreparationStateRel sourceProgram artifact target source)
    (hFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source)) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource (fuel + extra) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source) := by
  induction fuel generalizing target source extra with
  | zero =>
      change Simulation.Interaction.AllDone
        Assembly.InteractionSemantics.Finished
        (.done (.ok (.running source))) at hFinished
      cases hFinished with
      | done hDone => exact False.elim hDone
  | succ fuel ih =>
      have hFinishedSucc : Simulation.Interaction.AllDone
          Assembly.InteractionSemantics.Finished
          (Assembly.InteractionSemantics.Source.openRunNResult
            sourceProgram (fuel + 1) source) := by
        simpa [Nat.succ_eq_add_one] using hFinished
      rcases hBoundary with
        ⟨sourcePc, preparedPc, hPair, hSourcePc, hTargetPc, hRuntime⟩
      rcases hPair with hBlock | hEnd
      · rcases hBlock with
          ⟨block, hBlock, hBlockSource, hBlockPrepared⟩
        have hBlockSourcePc :
            source.pc = EvmYul.UInt256.ofNat block.sourcePc := by
          simpa [hBlockSource] using hSourcePc
        have hBlockTargetPc :
            target.pc = EvmYul.UInt256.ofNat block.preparedPc := by
          simpa [hBlockPrepared] using hTargetPc
        obtain ⟨stepFuel, hStepFuel, hStep⟩ :=
          compile?_preparationBlock_open_rel hCompile hBlock
            hBlockTargetPc hBlockSourcePc hRuntime
        have hSourceStep :=
          compile?_preparation_source_openStepResult_eq_block
            hCompile hBlock hBlockSourcePc
        have hFinishedExpanded := hFinishedSucc
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep] at hFinishedExpanded
        have hStepFinished :=
          Simulation.Interaction.AllDone.bind_inv hFinishedExpanded
        have hStepStrong :=
          Simulation.Interaction.Rel.strengthen_right hStep hStepFinished
        let remaining := fuel + (extra + (1 - stepFuel))
        have hFuel : Nat.succ fuel + extra = stepFuel + remaining := by
          dsimp [remaining]
          omega
        rw [hFuel,
          Assembly.InteractionSemantics.Source.openRunNResult_add]
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep]
        apply Simulation.Interaction.Rel.bind_custom hStepStrong
        intro targetDone sourceDone hDone
        rcases hDone with ⟨hRelated, hContinuationFinished⟩
        cases hRelated with
        | error hError => exact .done (.error hError)
        | ok hResult =>
            rename_i targetResult sourceResult
            cases targetResult with
            | running targetMid =>
                cases sourceResult with
                | running sourceMid =>
                    change PreparationStateRel sourceProgram artifact
                      targetMid sourceMid at hResult
                    change Simulation.Interaction.AllDone
                      Assembly.InteractionSemantics.Finished
                      (Assembly.InteractionSemantics.Source.openRunNResult
                        sourceProgram fuel sourceMid) at hContinuationFinished
                    exact ih (extra + (1 - stepFuel)) hResult
                      hContinuationFinished
                | halted sourceHalt =>
                    simp [PreparationStepResultRel] at hResult
            | halted targetHalt =>
                cases sourceResult with
                | running sourceMid =>
                    simp [PreparationStepResultRel] at hResult
                | halted sourceHalt =>
                    change targetHalt.kind = sourceHalt.kind /\
                      SameRuntimeData targetHalt.state sourceHalt.state /\
                        targetHalt.output = sourceHalt.output at hResult
                    exact .done (.ok hResult)
      · rcases hEnd with ⟨hSourceEnd, hPreparedEnd⟩
        have hArtifact := compile?_valid hCompile
        have hSourceToNat : source.pc.toNat = sourceProgram.byteLength := by
          rw [hSourcePc, hSourceEnd]
          exact hArtifact.sourcePCFits
        have hTargetToNat :
            target.pc.toNat = artifact.physicalSource.byteLength := by
          rw [hTargetPc, hPreparedEnd]
          exact hArtifact.physicalSourcePCFits
        have hSourceStep :
            Assembly.InteractionSemantics.Source.openStepResult
                sourceProgram source =
              .done (.error .InvalidInstruction) := by
          unfold Assembly.InteractionSemantics.Source.openStepResult
            Assembly.Source.stepResultWith
          rw [hSourceToNat, instrAtPc_end_eq_none]
          rfl
        have hTargetStep :
            Assembly.InteractionSemantics.Source.openStepResult
                artifact.physicalSource target =
              .done (.error .InvalidInstruction) := by
          unfold Assembly.InteractionSemantics.Source.openStepResult
            Assembly.Source.stepResultWith
          rw [hTargetToNat, instrAtPc_end_eq_none]
          rfl
        rw [show Nat.succ fuel + extra = (fuel + extra) + 1 by omega,
          Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hTargetStep]
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep]
        exact .done (.error rfl)

/-- Result interface for one branch of a fuel-bounded physical encoding. -/
def PrefixBranchResult
    (targetRun : Assembly.InteractionSemantics.OpenStepResult)
    (transcript : Simulation.Interaction.Transcript)
    (sourceDone : Assembly.Source.ExecutionOutcome) : Prop :=
  match sourceDone with
  | .ok (.running _) => Simulation.Interaction.Follows targetRun transcript
  | _ =>
      exists targetDone,
        Simulation.Interaction.Executes targetRun transcript targetDone /\
          RuntimeOutcomeRel targetDone sourceDone

/-- Branch-local preparation preservation. A source branch that exhausts its
instruction budget preserves its exact transcript prefix; an error or halt is
reproduced with a runtime-related outcome. -/
theorem compile?_preparation_openRunNResult_branch
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (fuel extra : Nat) {target source : EVMState}
    (hBoundary : PreparationStateRel sourceProgram artifact target source)
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Assembly.Source.ExecutionOutcome}
    (hExec : Simulation.Interaction.Executes
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source) transcript sourceDone) :
    PrefixBranchResult
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource (fuel + extra) target)
      transcript sourceDone := by
  induction fuel generalizing target source extra transcript sourceDone with
  | zero =>
      rw [Assembly.InteractionSemantics.Source.openRunNResult_zero] at hExec
      cases hExec
      unfold PrefixBranchResult
      exact Simulation.Interaction.Follows.nil _
  | succ fuel ih =>
      rcases hBoundary with
        ⟨sourcePc, preparedPc, hPair, hSourcePc, hTargetPc, hRuntime⟩
      rcases hPair with hBlock | hEnd
      · rcases hBlock with
          ⟨block, hBlock, hBlockSource, hBlockPrepared⟩
        have hBlockSourcePc :
            source.pc = EvmYul.UInt256.ofNat block.sourcePc := by
          simpa [hBlockSource] using hSourcePc
        have hBlockTargetPc :
            target.pc = EvmYul.UInt256.ofNat block.preparedPc := by
          simpa [hBlockPrepared] using hTargetPc
        obtain ⟨stepFuel, hStepFuel, hStep⟩ :=
          compile?_preparationBlock_open_rel hCompile hBlock
            hBlockTargetPc hBlockSourcePc hRuntime
        have hSourceStep :=
          compile?_preparation_source_openStepResult_eq_block
            hCompile hBlock hBlockSourcePc
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep] at hExec
        let remaining := fuel + (extra + (1 - stepFuel))
        have hFuel : Nat.succ fuel + extra = stepFuel + remaining := by
          dsimp [remaining]
          omega
        rcases Simulation.Interaction.Executes.bind_cases hExec with
          hStepError | hStepOk
        · rcases hStepError with ⟨sourceError, hDone, hSourceStepExec⟩
          subst sourceDone
          obtain ⟨targetDone, hTargetStepExec, hRelated⟩ :=
            Simulation.Interaction.Rel.executes
              (Simulation.Interaction.Rel.symm hStep) hSourceStepExec
          cases hRelated with
          | error hError =>
              rename_i targetError
              subst targetError
              have hTargetExec :=
                Assembly.InteractionSemantics.Source.openRunNResult_error_add_executes
                  (extra := remaining) hTargetStepExec
              rw [← hFuel] at hTargetExec
              exact ⟨.error sourceError, hTargetExec, .error rfl⟩
        · rcases hStepOk with
            ⟨sourceResult, headTranscript, restTranscript,
              hTranscript, hSourceStepExec, hRestExec⟩
          subst transcript
          obtain ⟨targetDone, hTargetStepExec, hRelated⟩ :=
            Simulation.Interaction.Rel.executes
              (Simulation.Interaction.Rel.symm hStep) hSourceStepExec
          cases hRelated with
          | ok hResult =>
              rename_i targetResult
              cases targetResult with
              | running targetMid =>
                  cases sourceResult with
                  | running sourceMid =>
                      change PreparationStateRel sourceProgram artifact
                        targetMid sourceMid at hResult
                      have hTail := ih (extra + (1 - stepFuel)) hResult hRestExec
                      unfold PrefixBranchResult at hTail ⊢
                      rw [hFuel,
                        Assembly.InteractionSemantics.Source.openRunNResult_add]
                      cases sourceDone with
                      | error sourceError =>
                          rcases hTail with
                            ⟨targetTailDone, hTargetTailExec, hTailRel⟩
                          exact
                            ⟨targetTailDone,
                              Simulation.Interaction.Executes.bind_ok
                                hTargetStepExec hTargetTailExec,
                              hTailRel⟩
                      | ok sourceFinal =>
                          cases sourceFinal with
                          | running sourceFinal =>
                              exact Simulation.Interaction.Follows.bind_ok
                                hTargetStepExec hTail
                          | halted sourceHalt =>
                              rcases hTail with
                                ⟨targetTailDone, hTargetTailExec, hTailRel⟩
                              exact
                                ⟨targetTailDone,
                                  Simulation.Interaction.Executes.bind_ok
                                    hTargetStepExec hTargetTailExec,
                                  hTailRel⟩
                  | halted sourceHalt =>
                      simp [PreparationStepResultRel] at hResult
              | halted targetHalt =>
                  cases sourceResult with
                  | running sourceMid =>
                      simp [PreparationStepResultRel] at hResult
                  | halted sourceHalt =>
                      cases hRestExec
                      have hTargetExec :=
                        Assembly.InteractionSemantics.Source.openRunNResult_halted_add_executes
                          (extra := remaining) hTargetStepExec
                      rw [← hFuel] at hTargetExec
                      exact
                        ⟨.ok (.halted targetHalt), by simpa using hTargetExec,
                          .ok hResult⟩
      · rcases hEnd with ⟨hSourceEnd, hPreparedEnd⟩
        have hArtifact := compile?_valid hCompile
        have hSourceToNat : source.pc.toNat = sourceProgram.byteLength := by
          rw [hSourcePc, hSourceEnd]
          exact hArtifact.sourcePCFits
        have hTargetToNat :
            target.pc.toNat = artifact.physicalSource.byteLength := by
          rw [hTargetPc, hPreparedEnd]
          exact hArtifact.physicalSourcePCFits
        have hSourceStep :
            Assembly.InteractionSemantics.Source.openStepResult
                sourceProgram source =
              .done (.error .InvalidInstruction) := by
          unfold Assembly.InteractionSemantics.Source.openStepResult
            Assembly.Source.stepResultWith
          rw [hSourceToNat, instrAtPc_end_eq_none]
          rfl
        have hTargetStep :
            Assembly.InteractionSemantics.Source.openStepResult
                artifact.physicalSource target =
              .done (.error .InvalidInstruction) := by
          unfold Assembly.InteractionSemantics.Source.openStepResult
            Assembly.Source.stepResultWith
          rw [hTargetToNat, instrAtPc_end_eq_none]
          rfl
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep] at hExec
        cases hExec
        have hTargetOne : Simulation.Interaction.Executes
            (Assembly.InteractionSemantics.Source.openRunNResult
              artifact.physicalSource 1 target) []
            (.error .InvalidInstruction) := by
          rw [Assembly.InteractionSemantics.Source.openRunNResult_one,
            hTargetStep]
          exact .done _
        have hTargetExec :=
          Assembly.InteractionSemantics.Source.openRunNResult_error_add_executes
            (extra := fuel + extra) hTargetOne
        rw [show 1 + (fuel + extra) = Nat.succ fuel + extra by omega]
          at hTargetExec
        exact ⟨.error .InvalidInstruction, hTargetExec, .error rfl⟩

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

/-- The compiler-sized invalid sentinel makes falloff stop before arbitrary
object payload bytes. -/
theorem compile?_sentinel_openStepResult
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (payload : List UInt8) {state : EVMState}
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (Program.codeByteLength artifact.program.code)) :
    openStepResult
        (Bytecode.ofList
          (artifact.bytes.toList ++ (encodeInstr (.prim .invalid) ++ payload)))
        state =
      .done (.error .InvalidInstruction) := by
  have hValid := compile?_valid hCompile
  have hBytes : artifact.bytes.toList =
      artifact.program.code.flatMap encodeLocated := by
    rw [hValid.bytes]
    simp [encode, Bytecode.ofList]
  have hLength : artifact.bytes.toList.length =
      Program.codeByteLength artifact.program.code := by
    rw [hBytes, flatMap_encodeLocated_length]
  have hSentinel := hValid.sentinelFits
  have hPcNat :
      (EvmYul.UInt256.ofNat artifact.bytes.toList.length).toNat =
        artifact.bytes.toList.length := by
    apply Bytecode.uint256_ofNat_toNat_of_decode_window
    rw [hLength]
    omega
  have hDecode :=
    decodeInstrAtPrefix artifact.bytes.toList payload (.prim .invalid)
      (by trivial) hPcNat
      (by rw [hLength]; omega)
      (by
        rw [hLength]
        simpa [Instr.byteSize] using hValid.sentinelFits)
  rcases hDecode with ⟨decoded, hDecodedInstr, hDecodedBytes⟩
  unfold openStepResult
  have hStatePc : state.pc =
      EvmYul.UInt256.ofNat artifact.bytes.toList.length := by
    rw [hPc, hLength]
  have hDecodedBytes' :
      EvmYul.EVM.decode
          (Bytecode.ofList
            (artifact.bytes.toList ++
              (encodeInstr (.prim .invalid) ++ payload)))
          (EvmYul.UInt256.ofNat artifact.bytes.toList.length) =
        some decoded := by
    simpa [List.append_assoc] using hDecodedBytes
  rw [hStatePc, hDecodedBytes']
  change
    (match Instr.ofDecoded? decoded.1 decoded.2 with
    | none => Simulation.Interaction.done (.error .InvalidInstruction)
    | some instr => instr.openStepResult state) =
      Simulation.Interaction.done (.error .InvalidInstruction)
  rw [Instr.ofDecoded?_of_decoded? (by trivial) hDecodedInstr]
  rfl

theorem openRunNResult_add (bytes : ByteArray) (first second : Nat)
    (state : EVMState) :
    openRunNResult bytes (first + second) state =
      (do
        let result <- openRunNResult bytes first state
        match result with
        | .running mid => openRunNResult bytes second mid
        | .halted halt => Simulation.Interaction.pure (.halted halt)) := by
  exact Assembly.InteractionSemantics.Control.openRunNResultWith_add
    (openStepResult bytes) first second state

theorem openRunNResult_error_add_executes
    {bytes : ByteArray} {fuel extra : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {error : EVMException}
    (hExec : Simulation.Interaction.Executes
      (openRunNResult bytes fuel state) transcript (.error error)) :
    Simulation.Interaction.Executes
      (openRunNResult bytes (fuel + extra) state)
      transcript (.error error) := by
  rw [openRunNResult_add]
  exact Simulation.Interaction.Executes.bind_error hExec

theorem openRunNResult_halted_add_executes
    {bytes : ByteArray} {fuel extra : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript} {halt : Halt}
    (hExec : Simulation.Interaction.Executes
      (openRunNResult bytes fuel state) transcript (.ok (.halted halt))) :
    Simulation.Interaction.Executes
      (openRunNResult bytes (fuel + extra) state)
      transcript (.ok (.halted halt)) := by
  rw [openRunNResult_add]
  have hCombined := Simulation.Interaction.Executes.bind_ok
    (next := fun result =>
      match result with
      | .running mid => openRunNResult bytes extra mid
      | .halted final => Simulation.Interaction.pure (.halted final))
    hExec
    (Simulation.Interaction.Executes.done
      (.ok (.halted halt) : Except EVMException StepResult))
  simpa using hCombined

theorem openRunNResult_succ (bytes : ByteArray) (fuel : Nat)
    (state : EVMState) :
    openRunNResult bytes (fuel + 1) state =
      (do
        let result <- openStepResult bytes state
        match result with
        | .running mid => openRunNResult bytes fuel mid
        | .halted halt => Simulation.Interaction.pure (.halted halt)) := rfl

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

theorem openStepResultEqInstrOfFetch
    {program : Program} {bytes : ByteArray} {pc : Nat}
    {instr : Instr} {state : EVMState}
    (hValid : program.Valid)
    (hDecode : DecodingCorrect program bytes)
    (hFetch : program.fetch pc = some instr)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    InteractionSemantics.openStepResult bytes state =
      instr.openStepResult state := by
  rcases Program.existsLocatedOfFetch hFetch with
    ⟨located, hMem, hLocatedPc, hInstr⟩
  subst instr
  exact
    openStepResultEqInstrOfDecodeAt
      ((List.forall_iff_forall_mem.mp hValid) located hMem)
      (hDecode.decodes located hMem)
      (by simpa [hLocatedPc] using hPc)

namespace InteractionSemantics

theorem openRunNResult_one_eq_instr
    {bytes : ByteArray} {pc : Nat} {instr : Instr} {state : EVMState}
    (hValid : instr.Valid)
    (hDecode : decodeAt bytes pc instr)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    openRunNResult bytes 1 state = instr.openStepResult state := by
  unfold openRunNResult Assembly.Control.runNResultWith
  rw [openStepResultEqInstrOfDecodeAt hValid hDecode hPc]
  simp only [Assembly.Control.runNResultWith]
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure (StepResult.running state')
        | .halted halt =>
            Simulation.Interaction.pure (StepResult.halted halt)) =
      (Simulation.Interaction.pure : StepResult ->
        Assembly.InteractionSemantics.OpenStepResult) := by
    funext result
    cases result <;> rfl
  change Simulation.Interaction.bind (instr.openStepResult state)
    (fun result =>
      match result with
      | .running state' =>
          Simulation.Interaction.pure (StepResult.running state')
      | .halted halt =>
          Simulation.Interaction.pure (StepResult.halted halt)) = _
  rw [hContinuation, Simulation.Interaction.bind_pure]

theorem openRunNResult_one_runningAt_next
    {bytes : ByteArray} {pc : Nat} {instr : Instr} {state : EVMState}
    (hValid : instr.Valid)
    (hSequential : instr.Sequential)
    (hDecode : decodeAt bytes pc instr)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Simulation.Interaction.AllDone
      (RunningAt (EvmYul.UInt256.ofNat (pc + instr.byteSize)))
      (openRunNResult bytes 1 state) := by
  rw [openRunNResult_one_eq_instr hValid hDecode hPc]
  simpa [hPc, UInt256_ofNat_add] using
    (Instr.openStepResult_runningAt_next
      (instr := instr) (state := state) hSequential)

theorem openRunNResult_one_runtimeRel
    {bytes : ByteArray} {pc : Nat} {instr : Instr}
    {target source : EVMState}
    (hValid : instr.Valid)
    (hIndependent : instr.PCIndependent)
    (hDecode : decodeAt bytes pc instr)
    (hPc : target.pc = EvmYul.UInt256.ofNat pc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult bytes 1 target)
      (Assembly.InteractionSemantics.Target.openStepInstrResult
        instr.toLogical source) := by
  unfold openRunNResult Assembly.Control.runNResultWith
  rw [openStepResultEqInstrOfDecodeAt hValid hDecode hPc]
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure (StepResult.running state')
        | .halted halt =>
            Simulation.Interaction.pure (StepResult.halted halt)) =
      (Simulation.Interaction.pure : StepResult ->
        Assembly.InteractionSemantics.OpenStepResult) := by
    funext result
    cases result <;> rfl
  simp only [Assembly.Control.runNResultWith]
  change Simulation.Interaction.Rel RuntimeOutcomeRel
    (Simulation.Interaction.bind (instr.openStepResult target)
      (fun result =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure (StepResult.running state')
        | .halted halt =>
            Simulation.Interaction.pure (StepResult.halted halt)))
    (Assembly.InteractionSemantics.Target.openStepInstrResult
      instr.toLogical source)
  rw [hContinuation, Simulation.Interaction.bind_pure]
  exact Instr.openStepResult_runtimeRel hIndependent hRel

theorem openRunNResult_one_source_rel
    {program : Assembly.Program} {sourcePc compactPc : Nat}
    {sourceInstr : Assembly.Instr} {compactInstr : Instr}
    {bytes : ByteArray} {target source : EVMState}
    (hInstr : SimpleSourceInstrRel sourceInstr compactInstr)
    (hValid : compactInstr.Valid)
    (hIndependent : compactInstr.PCIndependent)
    (hDecode : decodeAt bytes compactPc compactInstr)
    (hPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult bytes 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        program sourcePc sourceInstr source) := by
  rw [hInstr.openStepResult_eq program sourcePc source]
  exact
    openRunNResult_one_runtimeRel
      hValid hIndependent hDecode hPc hRel

theorem openRunNResult_one_source_boundary_rel
    {artifact : Artifact} {sourcePc compactPc : Nat}
    {sourceInstr : Assembly.Instr} {compactInstr : Instr}
    {bytes : ByteArray} {target source : EVMState}
    (hBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      (sourcePc + sourceInstr.byteSize)
      (compactPc + compactInstr.byteSize))
    (hInstr : SimpleSourceInstrRel sourceInstr compactInstr)
    (hValid : compactInstr.Valid)
    (hIndependent : compactInstr.PCIndependent)
    (hDecode : decodeAt bytes compactPc compactInstr)
    (hPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      (openRunNResult bytes 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource sourcePc sourceInstr source) := by
  apply runtimeRel_to_boundaryRel hBoundary
    (openRunNResult_one_source_rel hInstr hValid hIndependent
      hDecode hPc hRel)
  · exact openRunNResult_one_runningAt_next
      hValid hInstr.compactSequential hDecode hPc
  · simpa [hSourcePc, UInt256_ofNat_add] using
      hInstr.source_runningAt_next artifact.physicalSource sourcePc source

theorem openRunNResult_push_jump
    {bytes : ByteArray} {pc width : Nat} {dest : Word}
    {state : EVMState}
    (hFits : FitsWidth width dest.toNat)
    (hPushDecode : decodeAt bytes pc (.push width dest))
    (hJumpDecode : decodeAt bytes (pc + width + 1) .jump)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    openRunNResult bytes 2 state =
      .done (.ok (.running { state with pc := dest })) := by
  let afterPush :=
    state.replaceStackAndIncrPC (state.stack.push dest)
      (pcΔ := width + 1)
  unfold openRunNResult Assembly.Control.runNResultWith
  rw [openStepResultEqInstrOfDecodeAt
    (instr := .push width dest) hFits hPushDecode hPc]
  change Simulation.Interaction.bind
      (.done (.ok (StepResult.running afterPush))) _ = _
  simp only [Simulation.Interaction.bind]
  have hAfterPc :
      afterPush.pc = EvmYul.UInt256.ofNat (pc + width + 1) := by
    simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hPc, UInt256_ofNat_add,
      Nat.add_assoc]
  simp only [Assembly.Control.runNResultWith]
  rw [openStepResultEqInstrOfDecodeAt
    (instr := .jump) trivial hJumpDecode hAfterPc]
  rfl

theorem openRunNResult_push_jumpi
    {bytes : ByteArray} {pc width : Nat} {dest : Word}
    {state : EVMState}
    (hFits : FitsWidth width dest.toNat)
    (hPushDecode : decodeAt bytes pc (.push width dest))
    (hJumpDecode : decodeAt bytes (pc + width + 1) .jumpi)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    openRunNResult bytes 2 state =
      .done
        (match state.stack.pop with
        | some (stack, cond) =>
            .ok
              (.running
                { state with
                  pc := if cond != EvmYul.UInt256.ofNat 0 then
                    dest
                  else
                    EvmYul.UInt256.ofNat (pc + width + 2)
                  stack := stack })
        | none => .error .StackUnderflow) := by
  let afterPush :=
    state.replaceStackAndIncrPC (state.stack.push dest)
      (pcΔ := width + 1)
  unfold openRunNResult Assembly.Control.runNResultWith
  rw [openStepResultEqInstrOfDecodeAt
    (instr := .push width dest) hFits hPushDecode hPc]
  change Simulation.Interaction.bind
      (.done (.ok (StepResult.running afterPush))) _ = _
  simp only [Simulation.Interaction.bind]
  have hAfterPc :
      afterPush.pc = EvmYul.UInt256.ofNat (pc + width + 1) := by
    simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hPc, UInt256_ofNat_add,
      Nat.add_assoc]
  simp only [Assembly.Control.runNResultWith]
  rw [openStepResultEqInstrOfDecodeAt
    (instr := .jumpi) trivial hJumpDecode hAfterPc]
  cases hStack : state.stack with
  | nil =>
      simp [hStack, afterPush, Instr.openStepResult, Instr.openStep,
        Assembly.InteractionSemantics.Target.openStepInstr,
        Assembly.Target.stepInstrWith,
        Simulation.Interaction.bind,
        Simulation.Interaction.bind_done_ok,
        Simulation.Interaction.bind_done_error, Instr.haltKind?,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
        EvmYul.Stack.pop, EvmYul.Stack.pop2]
      rfl
  | cons cond stack =>
      simp [hStack, afterPush, Instr.openStepResult, Instr.openStep,
        Assembly.InteractionSemantics.Target.openStepInstr,
        Assembly.Target.stepInstrWith,
        Simulation.Interaction.bind,
        Simulation.Interaction.bind_done_ok,
        Simulation.Interaction.bind_done_error, Instr.haltKind?, hPc,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
        EvmYul.Stack.pop, EvmYul.Stack.pop2,
        hAfterPc, UInt256_ofNat_add, UInt256_add_assoc, Nat.add_assoc]
      rfl

theorem openRunNResult_push_jump_source_rel
    {sourceProgram : Assembly.Program} {sourcePc sourceDest : Nat}
    {label : Label} {bytes : ByteArray} {compactPc width : Nat}
    {compactDest : Word} {targetState sourceState : EVMState}
    (hSourceDest : sourceProgram.labelPc label = some sourceDest)
    (hFits : FitsWidth width compactDest.toNat)
    (hPushDecode : decodeAt bytes compactPc (.push width compactDest))
    (hJumpDecode : decodeAt bytes (compactPc + width + 1) .jump)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat compactPc)
    (hRel : SameRuntimeData targetState sourceState) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult bytes 2 targetState)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram sourcePc (.jump label) sourceState) := by
  rw [openRunNResult_push_jump hFits hPushDecode hJumpDecode hTargetPc]
  unfold Assembly.InteractionSemantics.Source.openStepAtResult
    Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
  simp [hSourceDest, Assembly.Source.jumpPc, Assembly.Instr.haltKind?,
    Simulation.Interaction.bind]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    SameRuntimeData.with_pc_right (EvmYul.UInt256.ofNat sourceDest)
      (SameRuntimeData.with_pc_left compactDest hRel)

theorem openRunNResult_push_jump_source_boundary_rel
    {artifact : Artifact} {sourcePc sourceDest compactPc compactDest width : Nat}
    {label : Label} {bytes : ByteArray} {targetState sourceState : EVMState}
    (hBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      sourceDest compactDest)
    (hSourceDest : artifact.physicalSource.labelPc label = some sourceDest)
    (hFits : FitsWidth width (EvmYul.UInt256.ofNat compactDest).toNat)
    (hPushDecode : decodeAt bytes compactPc
      (.push width (EvmYul.UInt256.ofNat compactDest)))
    (hJumpDecode : decodeAt bytes (compactPc + width + 1) .jump)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat compactPc)
    (hRel : SameRuntimeData targetState sourceState) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      (openRunNResult bytes 2 targetState)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource sourcePc (.jump label) sourceState) := by
  apply runtimeRel_to_boundaryRel hBoundary
    (openRunNResult_push_jump_source_rel hSourceDest hFits
      hPushDecode hJumpDecode hTargetPc hRel)
  · rw [openRunNResult_push_jump hFits hPushDecode hJumpDecode hTargetPc]
    exact .done rfl
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc, Assembly.Instr.haltKind?,
      Simulation.Interaction.bind]
    exact .done rfl

theorem openRunNResult_push_jumpi_source_rel
    {sourceProgram : Assembly.Program} {sourcePc sourceDest : Nat}
    {label : Label} {bytes : ByteArray} {compactPc width : Nat}
    {compactDest : Word} {targetState sourceState : EVMState}
    (hSourceDest : sourceProgram.labelPc label = some sourceDest)
    (hFits : FitsWidth width compactDest.toNat)
    (hPushDecode : decodeAt bytes compactPc (.push width compactDest))
    (hJumpDecode : decodeAt bytes (compactPc + width + 1) .jumpi)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat compactPc)
    (hRel : SameRuntimeData targetState sourceState) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult bytes 2 targetState)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram sourcePc (.jumpi label) sourceState) := by
  rw [openRunNResult_push_jumpi hFits hPushDecode hJumpDecode hTargetPc]
  unfold Assembly.InteractionSemantics.Source.openStepAtResult
    Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
  simp only [hSourceDest, Option.elim_some, Assembly.Instr.haltKind?,
    Simulation.Interaction.bind_done_ok]
  have hStack := SameRuntimeData.stack_eq hRel
  rw [hStack]
  cases hSourceStack : sourceState.stack with
  | nil =>
      simp [hSourceStack, EvmYul.Stack.pop]
      exact .done (.error rfl)
  | cons cond stack =>
      simp [hSourceStack, EvmYul.Stack.pop]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        SameRuntimeData.with_pc_right
          (if cond != EvmYul.UInt256.ofNat 0 then
            EvmYul.UInt256.ofNat sourceDest
          else Assembly.Source.jumpiFallthroughPc sourceState)
          (SameRuntimeData.with_pc_left
            (if cond != EvmYul.UInt256.ofNat 0 then
              compactDest
            else EvmYul.UInt256.ofNat (compactPc + width + 2))
            (SameRuntimeData.replaceStack
              (targetStack := stack) (sourceStack := stack) hRel rfl))

theorem openRunNResult_push_jumpi_source_boundary_rel
    {artifact : Artifact} {sourcePc sourceDest compactPc compactDest width : Nat}
    {label : Label} {bytes : ByteArray} {targetState sourceState : EVMState}
    (hTakenBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      sourceDest compactDest)
    (hNextBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      (sourcePc + (Assembly.Instr.jumpi label).byteSize)
      (compactPc + width + 2))
    (hSourceDest : artifact.physicalSource.labelPc label = some sourceDest)
    (hFits : FitsWidth width (EvmYul.UInt256.ofNat compactDest).toNat)
    (hPushDecode : decodeAt bytes compactPc
      (.push width (EvmYul.UInt256.ofNat compactDest)))
    (hJumpDecode : decodeAt bytes (compactPc + width + 1) .jumpi)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat compactPc)
    (hSourcePc : sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hRel : SameRuntimeData targetState sourceState) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      (openRunNResult bytes 2 targetState)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource sourcePc (.jumpi label) sourceState) := by
  have hRuntime := openRunNResult_push_jumpi_source_rel
    (sourcePc := sourcePc) hSourceDest hFits hPushDecode hJumpDecode
    hTargetPc hRel
  have hStack := SameRuntimeData.stack_eq hRel
  cases hSourceStack : sourceState.stack with
  | nil =>
      apply runtimeRel_to_boundaryRel hNextBoundary hRuntime
      · rw [openRunNResult_push_jumpi hFits hPushDecode hJumpDecode hTargetPc]
        rw [hStack, hSourceStack]
        exact .done trivial
      · unfold Assembly.InteractionSemantics.Source.openStepAtResult
          Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
        simp [hSourceDest, hSourceStack, Assembly.Instr.haltKind?]
        exact .done trivial
  | cons cond stack =>
      by_cases hCond : (cond != EvmYul.UInt256.ofNat 0) = true
      · apply runtimeRel_to_boundaryRel hTakenBoundary hRuntime
        · rw [openRunNResult_push_jumpi hFits hPushDecode hJumpDecode hTargetPc]
          rw [hStack, hSourceStack]
          exact .done (by simp [RunningAt, EvmYul.Stack.pop, hCond])
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
          simp [hSourceDest, hSourceStack, hCond,
            Assembly.Instr.haltKind?]
          exact .done (by simp [RunningAt, EvmYul.Stack.pop, hCond])
      · apply runtimeRel_to_boundaryRel hNextBoundary hRuntime
        · rw [openRunNResult_push_jumpi hFits hPushDecode hJumpDecode hTargetPc]
          rw [hStack, hSourceStack]
          exact .done (by simp [RunningAt, EvmYul.Stack.pop, hCond])
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt Assembly.Source.stepAt
          simp [hSourceDest, hSourceStack, hCond,
            Assembly.Source.jumpiFallthroughPc, Assembly.Instr.byteSize,
            Assembly.Instr.jumpSize, Assembly.Instr.push32Size,
            Assembly.Instr.haltKind?, hSourcePc,
            UInt256_ofNat_add, UInt256_add_assoc, Nat.add_assoc]
          exact .done (by simp [RunningAt, hCond])

/-- Compiler-selected one-source-instruction compact execution. Every block,
width, destination, and decoder fact is recovered from the checked artifact. -/
theorem compile?_sourceBlock_open_rel
    {source : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    {block : SourceBlock} {targetState sourceState : EVMState}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (suffix : List UInt8 := [])
    (hBlock : block ∈ artifact.blocks)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hSourcePc : sourceState.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : SameRuntimeData targetState sourceState) :
    ∃ targetFuel,
      targetFuel <= 2 ∧
        Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
          (openRunNResult
            (Bytecode.ofList (artifact.bytes.toList ++ suffix))
            targetFuel targetState)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            artifact.physicalSource block.sourcePc block.sourceInstr
            sourceState) := by
  have hArtifact := compile?_valid hCompile
  have hBlocks := compile?_blocksValid hCompile
  have hDecoding := compile?_decodingCorrect_with_suffix hCompile suffix
  obtain ⟨compactSize, hSize, hCode⟩ :=
    hBlocks.block_emit_of_mem hBlock
  have hNextBoundary := hBlocks.next_boundary hBlock hSize
  rw [(compile?_valid hCompile).blockCode] at hNextBoundary
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  cases sourceInstr with
  | label name =>
      simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?]
        at hSize hCode
      subst compactSize
      subst code
      let located : Located := { pc := compactPc, instr := .jumpdest }
      have hMem : located ∈ artifact.program.code :=
        hArtifact.mem_program_of_mem_block hBlock (by simp [located])
      exact
        ⟨1, by omega, openRunNResult_one_source_boundary_rel
          (sourcePc := sourcePc) (compactPc := compactPc)
          (sourceInstr := .label name) (compactInstr := .jumpdest)
          (by simpa using hNextBoundary)
          (SimpleSourceInstrRel.label name) trivial
          ((List.forall_iff_forall_mem.mp
            hArtifact.wellFormed.2.2.2) located hMem)
          (hDecoding.decodes located hMem) hTargetPc hSourcePc hRel⟩
  | prim op =>
      simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?]
        at hSize hCode
      subst compactSize
      subst code
      let located : Located := { pc := compactPc, instr := .prim op }
      have hMem : located ∈ artifact.program.code :=
        hArtifact.mem_program_of_mem_block hBlock (by simp [located])
      exact
        ⟨1, by omega, openRunNResult_one_source_boundary_rel
          (sourcePc := sourcePc) (compactPc := compactPc)
          (sourceInstr := .prim op) (compactInstr := .prim op)
          (by simpa using hNextBoundary)
          (SimpleSourceInstrRel.prim op) trivial
          ((List.forall_iff_forall_mem.mp
            hArtifact.wellFormed.2.2.2) located hMem)
          (hDecoding.decodes located hMem) hTargetPc hSourcePc hRel⟩
  | push value =>
      cases hWidth : pushWidthAt? artifact.pinnedPushPcs sourcePc value with
      | none => simp [sourceInstrSizeAt?, hWidth] at hSize
      | some width =>
          simp [sourceInstrSizeAt?, hWidth, emitSourceBlock?, emitInstrRev?]
            at hSize hCode
          subst compactSize
          subst code
          let located : Located :=
            { pc := compactPc, instr := .push width value }
          have hMem : located ∈ artifact.program.code :=
            hArtifact.mem_program_of_mem_block hBlock (by simp [located])
          exact
            ⟨1, by omega, openRunNResult_one_source_boundary_rel
              (sourcePc := sourcePc) (compactPc := compactPc)
              (sourceInstr := .push value)
              (compactInstr := .push width value)
              (by simpa using hNextBoundary)
              (SimpleSourceInstrRel.push width value)
              ((List.forall_iff_forall_mem.mp
                hArtifact.wellFormed.1) located hMem)
              ((List.forall_iff_forall_mem.mp
                hArtifact.wellFormed.2.2.2) located hMem)
              (hDecoding.decodes located hMem) hTargetPc hSourcePc hRel⟩
  | pushLabel target =>
      simp [sourceInstrSizeAt?] at hSize
  | jump target =>
      cases hDest : lookupLabel? artifact.labels target with
      | none =>
          simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some compactDest =>
          by_cases hFitsBool :
              fitsWidth? artifact.branchWidth compactDest = true
          · simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?,
              hDest, hFitsBool] at hSize hCode
            subst compactSize
            subst code
            obtain ⟨sourceDest, hSourceDest⟩ :=
              compile?_physical_labelPc_of_lookup hCompile hDest
            let pushLocated : Located :=
              { pc := compactPc
                instr := .push artifact.branchWidth
                  (EvmYul.UInt256.ofNat compactDest) }
            let jumpLocated : Located :=
              { pc := compactPc + artifact.branchWidth + 1
                instr := .jump }
            have hPushMem : pushLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hJumpMem : jumpLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hLabelBoundary :=
              compile?_label_boundary hCompile hSourceDest hDest
            exact
              ⟨2, by omega, openRunNResult_push_jump_source_boundary_rel
                hLabelBoundary hSourceDest
                ((List.forall_iff_forall_mem.mp
                  hArtifact.wellFormed.1) pushLocated hPushMem)
                (hDecoding.decodes pushLocated hPushMem)
                (hDecoding.decodes jumpLocated hJumpMem)
                hTargetPc hRel⟩
          · simp [emitSourceBlock?, emitInstrRev?, hDest, hFitsBool] at hCode
  | jumpi target =>
      cases hDest : lookupLabel? artifact.labels target with
      | none =>
          simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some compactDest =>
          by_cases hFitsBool :
              fitsWidth? artifact.branchWidth compactDest = true
          · simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?,
              hDest, hFitsBool] at hSize hCode
            subst compactSize
            subst code
            obtain ⟨sourceDest, hSourceDest⟩ :=
              compile?_physical_labelPc_of_lookup hCompile hDest
            let pushLocated : Located :=
              { pc := compactPc
                instr := .push artifact.branchWidth
                  (EvmYul.UInt256.ofNat compactDest) }
            let jumpLocated : Located :=
              { pc := compactPc + artifact.branchWidth + 1
                instr := .jumpi }
            have hPushMem : pushLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hJumpMem : jumpLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hLabelBoundary :=
              compile?_label_boundary hCompile hSourceDest hDest
            exact
              ⟨2, by omega, openRunNResult_push_jumpi_source_boundary_rel
                hLabelBoundary
                (by simpa [Assembly.Instr.byteSize, Assembly.Instr.jumpSize,
                    Nat.add_assoc] using hNextBoundary)
                hSourceDest
                ((List.forall_iff_forall_mem.mp
                  hArtifact.wellFormed.1) pushLocated hPushMem)
                (hDecoding.decodes pushLocated hPushMem)
                (hDecoding.decodes jumpLocated hJumpMem)
                hTargetPc hSourcePc hRel⟩
          · simp [emitSourceBlock?, emitInstrRev?, hDest, hFitsBool] at hCode
  | jumpDynamic =>
      simp [sourceInstrSizeAt?] at hSize

/-- A terminal wide-Assembly run is simulated by actual compact bytes with a
uniform two-opcode budget per source instruction. The extra budget is useful
for composition: one-opcode blocks leave one unit that is inert once every
open-world branch has halted. -/
theorem compile?_openRunNResult_terminal_rel
    {input : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? input pinnedPushPcs = some artifact)
    (suffix : List UInt8 := [])
    (fuel extra : Nat) {target source : EVMState}
    (hBoundary : BoundaryStateRel artifact target source)
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source)) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult
        (Bytecode.ofList (artifact.bytes.toList ++ suffix))
        (2 * fuel + extra) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source) := by
  induction fuel generalizing target source extra with
  | zero =>
      change Simulation.Interaction.AllDone
        Assembly.InteractionSemantics.Terminal
        (.done (.ok (.running source))) at hTerminal
      cases hTerminal with
      | done hDone => exact False.elim hDone
  | succ fuel ih =>
      have hTerminalSucc : Simulation.Interaction.AllDone
          Assembly.InteractionSemantics.Terminal
          (Assembly.InteractionSemantics.Source.openRunNResult
            artifact.physicalSource (fuel + 1) source) := by
        simpa [Nat.succ_eq_add_one] using hTerminal
      obtain ⟨block, hBlock, hSourcePc, hTargetPc, hRuntime⟩ :=
        hBoundary.active_of_terminal_succ hCompile hTerminalSucc
      obtain ⟨stepFuel, hStepFuel, hStep⟩ :=
        compile?_sourceBlock_open_rel hCompile suffix hBlock
          hTargetPc hSourcePc hRuntime
      have hSourceStep :=
        compile?_source_openStepResult_eq_block hCompile hBlock hSourcePc
      have hTerminalExpanded := hTerminalSucc
      rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
        hSourceStep] at hTerminalExpanded
      have hStepTerminal :=
        Simulation.Interaction.AllDone.bind_inv hTerminalExpanded
      have hStepStrong :=
        Simulation.Interaction.Rel.strengthen_right hStep hStepTerminal
      let remaining := 2 * fuel + (extra + (2 - stepFuel))
      have hFuel : 2 * Nat.succ fuel + extra = stepFuel + remaining := by
        dsimp [remaining]
        omega
      rw [hFuel, openRunNResult_add]
      rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
        hSourceStep]
      apply Simulation.Interaction.Rel.bind_custom hStepStrong
      intro targetDone sourceDone hDone
      rcases hDone with ⟨hRelated, hContinuationTerminal⟩
      cases hRelated with
      | error hError =>
          exact False.elim hContinuationTerminal
      | ok hResult =>
          rename_i targetResult sourceResult
          cases targetResult with
          | running targetMid =>
              cases sourceResult with
              | running sourceMid =>
                  change BoundaryStateRel artifact targetMid sourceMid at hResult
                  change Simulation.Interaction.AllDone
                    Assembly.InteractionSemantics.Terminal
                    (Assembly.InteractionSemantics.Source.openRunNResult
                      artifact.physicalSource fuel sourceMid) at hContinuationTerminal
                  exact ih (extra + (2 - stepFuel)) hResult
                    hContinuationTerminal
              | halted sourceHalt =>
                  simp [BoundaryStepResultRel] at hResult
          | halted targetHalt =>
              cases sourceResult with
              | running sourceMid =>
                  simp [BoundaryStepResultRel] at hResult
              | halted sourceHalt =>
                  change targetHalt.kind = sourceHalt.kind ∧
                    SameRuntimeData targetHalt.state sourceHalt.state ∧
                      targetHalt.output = sourceHalt.output at hResult
                  exact .done (.ok hResult)

/-- Compact encoding preserves every finished branch when an invalid sentinel
separates code from arbitrary object payload bytes. -/
theorem compile?_openRunNResult_finished_rel
    {input : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? input pinnedPushPcs = some artifact)
    (payload : List UInt8) (fuel extra : Nat) {target source : EVMState}
    (hBoundary : BoundaryStateRel artifact target source)
    (hFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source)) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult
        (Bytecode.ofList
          (artifact.bytes.toList ++ (encodeInstr (.prim .invalid) ++ payload)))
        (2 * fuel + extra) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source) := by
  induction fuel generalizing target source extra with
  | zero =>
      change Simulation.Interaction.AllDone
        Assembly.InteractionSemantics.Finished
        (.done (.ok (.running source))) at hFinished
      cases hFinished with
      | done hDone => exact False.elim hDone
  | succ fuel ih =>
      have hFinishedSucc : Simulation.Interaction.AllDone
          Assembly.InteractionSemantics.Finished
          (Assembly.InteractionSemantics.Source.openRunNResult
            artifact.physicalSource (fuel + 1) source) := by
        simpa [Nat.succ_eq_add_one] using hFinished
      rcases hBoundary with
        ⟨sourcePc, compactPc, hPair, hSourcePc, hTargetPc, hRuntime⟩
      rcases hPair with hBlock | hEnd
      · rcases hBlock with
          ⟨block, hBlock, hBlockSource, hBlockCompact⟩
        have hBlockSourcePc :
            source.pc = EvmYul.UInt256.ofNat block.sourcePc := by
          simpa [hBlockSource] using hSourcePc
        have hBlockTargetPc :
            target.pc = EvmYul.UInt256.ofNat block.compactPc := by
          simpa [hBlockCompact] using hTargetPc
        obtain ⟨stepFuel, hStepFuel, hStep⟩ :=
          compile?_sourceBlock_open_rel hCompile
            (encodeInstr (.prim .invalid) ++ payload) hBlock
            hBlockTargetPc hBlockSourcePc hRuntime
        have hSourceStep :=
          compile?_source_openStepResult_eq_block
            hCompile hBlock hBlockSourcePc
        have hFinishedExpanded := hFinishedSucc
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep] at hFinishedExpanded
        have hStepFinished :=
          Simulation.Interaction.AllDone.bind_inv hFinishedExpanded
        have hStepStrong :=
          Simulation.Interaction.Rel.strengthen_right hStep hStepFinished
        let remaining := 2 * fuel + (extra + (2 - stepFuel))
        have hFuel : 2 * Nat.succ fuel + extra = stepFuel + remaining := by
          dsimp [remaining]
          omega
        rw [hFuel, openRunNResult_add]
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep]
        apply Simulation.Interaction.Rel.bind_custom hStepStrong
        intro targetDone sourceDone hDone
        rcases hDone with ⟨hRelated, hContinuationFinished⟩
        cases hRelated with
        | error hError => exact .done (.error hError)
        | ok hResult =>
            rename_i targetResult sourceResult
            cases targetResult with
            | running targetMid =>
                cases sourceResult with
                | running sourceMid =>
                    change BoundaryStateRel artifact targetMid sourceMid at hResult
                    change Simulation.Interaction.AllDone
                      Assembly.InteractionSemantics.Finished
                      (Assembly.InteractionSemantics.Source.openRunNResult
                        artifact.physicalSource fuel sourceMid) at hContinuationFinished
                    exact ih (extra + (2 - stepFuel)) hResult
                      hContinuationFinished
                | halted sourceHalt =>
                    simp [BoundaryStepResultRel] at hResult
            | halted targetHalt =>
                cases sourceResult with
                | running sourceMid =>
                    simp [BoundaryStepResultRel] at hResult
                | halted sourceHalt =>
                    change targetHalt.kind = sourceHalt.kind /\
                      SameRuntimeData targetHalt.state sourceHalt.state /\
                        targetHalt.output = sourceHalt.output at hResult
                    exact .done (.ok hResult)
      · rcases hEnd with ⟨hSourceEnd, hCompactEnd⟩
        have hArtifact := compile?_valid hCompile
        have hSourceToNat :
            source.pc.toNat = artifact.physicalSource.byteLength := by
          rw [hSourcePc, hSourceEnd]
          exact hArtifact.physicalSourcePCFits
        have hSourceStep :
            Assembly.InteractionSemantics.Source.openStepResult
                artifact.physicalSource source =
              .done (.error .InvalidInstruction) := by
          unfold Assembly.InteractionSemantics.Source.openStepResult
            Assembly.Source.stepResultWith
          rw [hSourceToNat, instrAtPc_end_eq_none]
          rfl
        have hTargetStep :
            openStepResult
                (Bytecode.ofList
                  (artifact.bytes.toList ++
                    (encodeInstr (.prim .invalid) ++ payload))) target =
              .done (.error .InvalidInstruction) := by
          simpa [List.append_assoc] using
            (compile?_sentinel_openStepResult hCompile payload
              (state := target)
              (by simpa [hCompactEnd] using hTargetPc))
        rw [show 2 * Nat.succ fuel + extra =
            (2 * fuel + extra + 1) + 1 by omega]
        rw [openRunNResult_succ]
        rw [hTargetStep]
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep]
        exact .done (.error rfl)

/-- Branch-local preservation from the prepared physical Assembly program to
its decoded compact bytecode image. -/
theorem compile?_openRunNResult_branch
    {input : Assembly.Program} {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? input pinnedPushPcs = some artifact)
    (payload : List UInt8) (fuel extra : Nat) {target source : EVMState}
    (hBoundary : BoundaryStateRel artifact target source)
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Assembly.Source.ExecutionOutcome}
    (hExec : Simulation.Interaction.Executes
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source) transcript sourceDone) :
    PrefixBranchResult
      (openRunNResult
        (Bytecode.ofList
          (artifact.bytes.toList ++ (encodeInstr (.prim .invalid) ++ payload)))
        (2 * fuel + extra) target)
      transcript sourceDone := by
  induction fuel generalizing target source extra transcript sourceDone with
  | zero =>
      rw [Assembly.InteractionSemantics.Source.openRunNResult_zero] at hExec
      cases hExec
      unfold PrefixBranchResult
      exact Simulation.Interaction.Follows.nil _
  | succ fuel ih =>
      rcases hBoundary with
        ⟨sourcePc, compactPc, hPair, hSourcePc, hTargetPc, hRuntime⟩
      rcases hPair with hBlock | hEnd
      · rcases hBlock with
          ⟨block, hBlock, hBlockSource, hBlockCompact⟩
        have hBlockSourcePc :
            source.pc = EvmYul.UInt256.ofNat block.sourcePc := by
          simpa [hBlockSource] using hSourcePc
        have hBlockTargetPc :
            target.pc = EvmYul.UInt256.ofNat block.compactPc := by
          simpa [hBlockCompact] using hTargetPc
        obtain ⟨stepFuel, hStepFuel, hStep⟩ :=
          compile?_sourceBlock_open_rel hCompile
            (encodeInstr (.prim .invalid) ++ payload) hBlock
            hBlockTargetPc hBlockSourcePc hRuntime
        have hSourceStep :=
          compile?_source_openStepResult_eq_block
            hCompile hBlock hBlockSourcePc
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep] at hExec
        let remaining := 2 * fuel + (extra + (2 - stepFuel))
        have hFuel : 2 * Nat.succ fuel + extra = stepFuel + remaining := by
          dsimp [remaining]
          omega
        rcases Simulation.Interaction.Executes.bind_cases hExec with
          hStepError | hStepOk
        · rcases hStepError with ⟨sourceError, hDone, hSourceStepExec⟩
          subst sourceDone
          obtain ⟨targetDone, hTargetStepExec, hRelated⟩ :=
            Simulation.Interaction.Rel.executes
              (Simulation.Interaction.Rel.symm hStep) hSourceStepExec
          cases hRelated with
          | error hError =>
              rename_i targetError
              subst targetError
              have hTargetExec := openRunNResult_error_add_executes
                (extra := remaining) hTargetStepExec
              rw [← hFuel] at hTargetExec
              exact ⟨.error sourceError, hTargetExec, .error rfl⟩
        · rcases hStepOk with
            ⟨sourceResult, headTranscript, restTranscript,
              hTranscript, hSourceStepExec, hRestExec⟩
          subst transcript
          obtain ⟨targetDone, hTargetStepExec, hRelated⟩ :=
            Simulation.Interaction.Rel.executes
              (Simulation.Interaction.Rel.symm hStep) hSourceStepExec
          cases hRelated with
          | ok hResult =>
              rename_i targetResult
              cases targetResult with
              | running targetMid =>
                  cases sourceResult with
                  | running sourceMid =>
                      change BoundaryStateRel artifact targetMid sourceMid
                        at hResult
                      have hTail := ih (extra + (2 - stepFuel)) hResult hRestExec
                      unfold PrefixBranchResult at hTail ⊢
                      rw [hFuel, openRunNResult_add]
                      cases sourceDone with
                      | error sourceError =>
                          rcases hTail with
                            ⟨targetTailDone, hTargetTailExec, hTailRel⟩
                          exact
                            ⟨targetTailDone,
                              Simulation.Interaction.Executes.bind_ok
                                hTargetStepExec hTargetTailExec,
                              hTailRel⟩
                      | ok sourceFinal =>
                          cases sourceFinal with
                          | running sourceFinal =>
                              exact Simulation.Interaction.Follows.bind_ok
                                hTargetStepExec hTail
                          | halted sourceHalt =>
                              rcases hTail with
                                ⟨targetTailDone, hTargetTailExec, hTailRel⟩
                              exact
                                ⟨targetTailDone,
                                  Simulation.Interaction.Executes.bind_ok
                                    hTargetStepExec hTargetTailExec,
                                  hTailRel⟩
                  | halted sourceHalt =>
                      simp [BoundaryStepResultRel] at hResult
              | halted targetHalt =>
                  cases sourceResult with
                  | running sourceMid =>
                      simp [BoundaryStepResultRel] at hResult
                  | halted sourceHalt =>
                      cases hRestExec
                      have hTargetExec := openRunNResult_halted_add_executes
                        (extra := remaining) hTargetStepExec
                      rw [← hFuel] at hTargetExec
                      exact
                        ⟨.ok (.halted targetHalt), by simpa using hTargetExec,
                          .ok hResult⟩
      · rcases hEnd with ⟨hSourceEnd, hCompactEnd⟩
        have hArtifact := compile?_valid hCompile
        have hSourceToNat :
            source.pc.toNat = artifact.physicalSource.byteLength := by
          rw [hSourcePc, hSourceEnd]
          exact hArtifact.physicalSourcePCFits
        have hSourceStep :
            Assembly.InteractionSemantics.Source.openStepResult
                artifact.physicalSource source =
              .done (.error .InvalidInstruction) := by
          unfold Assembly.InteractionSemantics.Source.openStepResult
            Assembly.Source.stepResultWith
          rw [hSourceToNat, instrAtPc_end_eq_none]
          rfl
        have hTargetStep :
            openStepResult
                (Bytecode.ofList
                  (artifact.bytes.toList ++
                    (encodeInstr (.prim .invalid) ++ payload))) target =
              .done (.error .InvalidInstruction) := by
          simpa [List.append_assoc] using
            (compile?_sentinel_openStepResult hCompile payload
              (state := target)
              (by simpa [hCompactEnd] using hTargetPc))
        rw [Assembly.InteractionSemantics.Source.openRunNResult_succ,
          hSourceStep] at hExec
        cases hExec
        have hTargetOne : Simulation.Interaction.Executes
            (openRunNResult
              (Bytecode.ofList
                (artifact.bytes.toList ++
                  (encodeInstr (.prim .invalid) ++ payload))) 1 target)
            [] (.error .InvalidInstruction) := by
          rw [openRunNResult_succ, hTargetStep]
          exact .done _
        have hTargetExec := openRunNResult_error_add_executes
          (extra := 2 * fuel + extra + 1) hTargetOne
        rw [show 1 + (2 * fuel + extra + 1) =
            2 * Nat.succ fuel + extra by omega] at hTargetExec
        exact ⟨.error .InvalidInstruction, hTargetExec, .error rfl⟩

theorem stepResultRuntimeRel_trans
    {first second third : StepResult}
    (hFirst : StepResultRuntimeRel first second)
    (hSecond : StepResultRuntimeRel second third) :
    StepResultRuntimeRel first third := by
  cases first with
  | running firstState =>
      cases second with
      | running secondState =>
          cases third with
          | running thirdState =>
              exact SameRuntimeData.trans hFirst hSecond
          | halted thirdHalt =>
              exact False.elim hSecond
      | halted secondHalt =>
          exact False.elim hFirst
  | halted firstHalt =>
      cases second with
      | running secondState =>
          exact False.elim hFirst
      | halted secondHalt =>
          cases third with
          | running thirdState =>
              exact False.elim hSecond
          | halted thirdHalt =>
              exact
                ⟨Eq.trans hFirst.1 hSecond.1,
                  SameRuntimeData.trans hFirst.2.1 hSecond.2.1,
                  Eq.trans hFirst.2.2 hSecond.2.2⟩

theorem runtimeOutcomeRel_trans
    {first second third : Except EVMException StepResult}
    (hFirst : RuntimeOutcomeRel first second)
    (hSecond : RuntimeOutcomeRel second third) :
    RuntimeOutcomeRel first third := by
  cases hFirst with
  | error hFirstError =>
      cases hSecond with
      | error hSecondError =>
          exact .error (hFirstError.trans hSecondError)
  | ok hFirstResult =>
      cases hSecond with
      | ok hSecondResult =>
          exact .ok (stepResultRuntimeRel_trans hFirstResult hSecondResult)

namespace PrefixBranchResult

theorem follows
    {targetRun : Assembly.InteractionSemantics.OpenStepResult}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Assembly.Source.ExecutionOutcome}
    (hResult : PrefixBranchResult targetRun transcript sourceDone) :
    Simulation.Interaction.Follows targetRun transcript := by
  cases sourceDone with
  | error sourceError =>
      rcases hResult with ⟨targetDone, hExec, _hRel⟩
      exact hExec.follows
  | ok sourceResult =>
      cases sourceResult with
      | running sourceFinal => exact hResult
      | halted sourceHalt =>
          rcases hResult with ⟨targetDone, hExec, _hRel⟩
          exact hExec.follows

/-- Compose two branch-local physical encodings without inspecting or
constraining the suffix after a source running prefix. -/
theorem trans
    {middleRun targetRun :
      Assembly.InteractionSemantics.OpenStepResult}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Assembly.Source.ExecutionOutcome}
    (hFirst : PrefixBranchResult middleRun transcript sourceDone)
    (hSecond : forall nextTranscript middleDone,
      Simulation.Interaction.Executes middleRun nextTranscript middleDone ->
        PrefixBranchResult targetRun nextTranscript middleDone) :
    PrefixBranchResult targetRun transcript sourceDone := by
  cases sourceDone with
  | error sourceError =>
      rcases hFirst with ⟨middleDone, hMiddleExec, hFirstRel⟩
      have hTarget := hSecond transcript middleDone hMiddleExec
      cases hFirstRel with
      | error hFirstError =>
          rcases hTarget with ⟨targetDone, hTargetExec, hSecondRel⟩
          exact
            ⟨targetDone, hTargetExec,
              runtimeOutcomeRel_trans hSecondRel (.error hFirstError)⟩
  | ok sourceResult =>
      cases sourceResult with
      | running sourceFinal =>
          obtain ⟨suffix, middleDone, hMiddleExec⟩ :=
            hFirst.exists_executes_extension
          have hTarget :=
            hSecond (transcript ++ suffix) middleDone hMiddleExec
          cases middleDone with
          | error middleError =>
              rcases hTarget with ⟨targetDone, hTargetExec, _hRel⟩
              exact Simulation.Interaction.Follows.prefix_of_append
                transcript suffix hTargetExec.follows
          | ok middleResult =>
              cases middleResult with
              | running middleFinal =>
                  exact Simulation.Interaction.Follows.prefix_of_append
                    transcript suffix hTarget
              | halted middleHalt =>
                  rcases hTarget with ⟨targetDone, hTargetExec, _hRel⟩
                  exact Simulation.Interaction.Follows.prefix_of_append
                    transcript suffix hTargetExec.follows
      | halted sourceHalt =>
          rcases hFirst with ⟨middleDone, hMiddleExec, hFirstRel⟩
          have hTarget := hSecond transcript middleDone hMiddleExec
          cases middleDone with
          | error middleError => cases hFirstRel
          | ok middleResult =>
              cases middleResult with
              | running middleFinal =>
                  cases hFirstRel with
                  | ok hFirstResult => cases hFirstResult
              | halted middleHalt =>
                  cases hFirstRel with
                  | ok hFirstResult =>
                      rcases hTarget with
                        ⟨targetDone, hTargetExec, hSecondRel⟩
                      exact
                        ⟨targetDone, hTargetExec,
                          runtimeOutcomeRel_trans hSecondRel
                            (.ok hFirstResult)⟩

end PrefixBranchResult

/-- Complete branch-local Assembly-to-compact-bytecode preservation. The
preparation and physical encoding passes remain adjacent owners and compose
only through their runtime relation and finite-prefix interface. -/
theorem compile?_source_openRunNResult_branch
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (payload : List UInt8) (fuel : Nat) {target source : EVMState}
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat 0)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat 0)
    (hInitial : SameRuntimeData target source)
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Assembly.Source.ExecutionOutcome}
    (hExec : Simulation.Interaction.Executes
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source) transcript sourceDone) :
    PrefixBranchResult
      (openRunNResult
        (Bytecode.ofList
          (artifact.bytes.toList ++ (encodeInstr (.prim .invalid) ++ payload)))
        (2 * fuel) target)
      transcript sourceDone := by
  have hPreparationBoundary :
      PreparationStateRel sourceProgram artifact source source :=
    ⟨0, 0,
      (by simpa using
        (compile?_preparationBlocksValid hCompile).initial_boundary),
      hSourcePc, hSourcePc, SameRuntimeData.refl source⟩
  have hPreparation :=
    compile?_preparation_openRunNResult_branch
      hCompile fuel 0 hPreparationBoundary hExec
  have hCompactBoundary : BoundaryStateRel artifact target source :=
    ⟨0, 0, compile?_initial_boundary hCompile,
      hSourcePc, hTargetPc, hInitial⟩
  apply PrefixBranchResult.trans
    (targetRun := openRunNResult
      (Bytecode.ofList
        (artifact.bytes.toList ++ (encodeInstr (.prim .invalid) ++ payload)))
      (2 * fuel) target)
    (by simpa using hPreparation)
  intro nextTranscript middleDone hMiddleExec
  simpa using
    (compile?_openRunNResult_branch hCompile payload fuel 0
      hCompactBoundary hMiddleExec)

theorem runtimeOutcomeRel_terminal_left
    {target source : Except EVMException StepResult}
    (hRel : RuntimeOutcomeRel target source)
    (hTerminal : Assembly.InteractionSemantics.Terminal source) :
    Assembly.InteractionSemantics.Terminal target := by
  cases hRel with
  | error hError => exact False.elim hTerminal
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult <;> cases sourceResult <;>
        simp_all [StepResultRuntimeRel,
          Assembly.InteractionSemantics.Terminal, StepResult.IsTerminal]

theorem runtimeOutcomeRel_finished_left
    {target source : Except EVMException StepResult}
    (hRel : RuntimeOutcomeRel target source)
    (hFinished : Assembly.InteractionSemantics.Finished source) :
    Assembly.InteractionSemantics.Finished target := by
  cases hRel with
  | error hError => trivial
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult <;> cases sourceResult <;>
        simp_all [StepResultRuntimeRel,
          Assembly.InteractionSemantics.Finished, StepResult.IsTerminal]

/-- The complete Assembly-owned compact boundary. Preprocessing and variable-
width encoding remain adjacent subproofs, while this theorem only composes
their exact open interaction trees. -/
theorem compile?_source_openRunNResult_terminal_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (suffix : List UInt8 := [])
    (fuel extra : Nat) {target source : EVMState}
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat 0)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat 0)
    (hInitial : SameRuntimeData target source)
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source)) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult
        (Bytecode.ofList (artifact.bytes.toList ++ suffix))
        (2 * fuel + extra) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source) := by
  have hPreparationBoundary :
      PreparationStateRel sourceProgram artifact source source :=
    ⟨0, 0,
      (by simpa using
        (compile?_preparationBlocksValid hCompile).initial_boundary),
      hSourcePc, hSourcePc, SameRuntimeData.refl source⟩
  have hPreparation :=
    compile?_preparation_openRunNResult_terminal_rel
      hCompile fuel 0 hPreparationBoundary hTerminal
  have hPhysicalTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left
      (Simulation.Interaction.Rel.symm hPreparation) hTerminal
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    exact runtimeOutcomeRel_terminal_left hDone.1 hDone.2
  have hCompactBoundary : BoundaryStateRel artifact target source :=
    ⟨0, 0, compile?_initial_boundary hCompile,
      hSourcePc, hTargetPc, hInitial⟩
  have hCompact := compile?_openRunNResult_terminal_rel
    hCompile suffix fuel extra hCompactBoundary hPhysicalTerminal
  apply Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hCompact hPreparation)
  intro targetDone sourceDone hDone
  rcases hDone with ⟨middleDone, hTargetMiddle, hMiddleSource⟩
  exact runtimeOutcomeRel_trans hTargetMiddle hMiddleSource

/-- The complete all-finished Assembly-owned compact boundary. A checked
invalid sentinel separates executable bytes from arbitrary object payload. -/
theorem compile?_source_openRunNResult_finished_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? sourceProgram pinnedPushPcs = some artifact)
    (payload : List UInt8) (fuel extra : Nat) {target source : EVMState}
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat 0)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat 0)
    (hInitial : SameRuntimeData target source)
    (hFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source)) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (openRunNResult
        (Bytecode.ofList
          (artifact.bytes.toList ++ (encodeInstr (.prim .invalid) ++ payload)))
        (2 * fuel + extra) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram fuel source) := by
  have hPreparationBoundary :
      PreparationStateRel sourceProgram artifact source source :=
    ⟨0, 0,
      (by simpa using
        (compile?_preparationBlocksValid hCompile).initial_boundary),
      hSourcePc, hSourcePc, SameRuntimeData.refl source⟩
  have hPreparation :=
    compile?_preparation_openRunNResult_finished_rel
      hCompile fuel 0 hPreparationBoundary hFinished
  have hPhysicalFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource fuel source) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left
      (Simulation.Interaction.Rel.symm hPreparation) hFinished
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    exact runtimeOutcomeRel_finished_left hDone.1 hDone.2
  have hCompactBoundary : BoundaryStateRel artifact target source :=
    ⟨0, 0, compile?_initial_boundary hCompile,
      hSourcePc, hTargetPc, hInitial⟩
  have hCompact := compile?_openRunNResult_finished_rel
    hCompile payload fuel extra hCompactBoundary hPhysicalFinished
  apply Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hCompact hPreparation)
  intro targetDone sourceDone hDone
  rcases hDone with ⟨middleDone, hTargetMiddle, hMiddleSource⟩
  exact runtimeOutcomeRel_trans hTargetMiddle hMiddleSource

end InteractionSemantics

end Compact
end Assembly
end EvmCompiler
