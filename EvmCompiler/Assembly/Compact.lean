import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.InteractionPreservation
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

def codeByteLength : List Located -> Nat
  | [] => 0
  | located :: rest => located.instr.byteSize + codeByteLength rest

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

def valid? (program : Program) : Bool :=
  program.code.all fun located => located.instr.valid?

def pcIndependent? (program : Program) : Bool :=
  program.code.all fun located => located.instr.pcIndependent?

def wellFormed? (program : Program) : Bool :=
  program.valid? && layoutFrom? program.code 0 &&
    decide (Program.codeByteLength program.code < 18446744073709551616) &&
      program.pcIndependent?

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

structure SourceBlock where
  sourcePc : Nat
  compactPc : Nat
  sourceInstr : Assembly.Instr
  code : List Located
  deriving DecidableEq, Repr

def emitSourceBlock? (branchWidth compactPc : Nat) (table : LabelTable)
    (instr : Assembly.Instr) : Option (List Located) := do
  let reversed <- emitInstrRev? branchWidth compactPc table instr []
  some reversed.reverse

def emitBlocksFrom? (branchWidth : Nat) (table : LabelTable) :
    Assembly.Program -> Nat -> Nat -> Option (List SourceBlock)
  | [], _sourcePc, _compactPc => some []
  | instr :: rest, sourcePc, compactPc => do
      let compactSize <- sourceInstrSize? branchWidth instr
      let code <- emitSourceBlock? branchWidth compactPc table instr
      let blocks <-
        emitBlocksFrom? branchWidth table rest
          (sourcePc + instr.byteSize) (compactPc + compactSize)
      some
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: blocks)

def emitBlocks? (source : Assembly.Program) (branchWidth : Nat)
    (table : LabelTable) : Option (List SourceBlock) :=
  emitBlocksFrom? branchWidth table source 0 0

def blocksCode (blocks : List SourceBlock) : List Located :=
  blocks.flatMap SourceBlock.code

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

inductive BlocksValidFrom (branchWidth : Nat) (table : LabelTable) :
    Assembly.Program -> Nat -> Nat -> List SourceBlock -> Prop
  | nil (sourcePc compactPc : Nat) :
      BlocksValidFrom branchWidth table [] sourcePc compactPc []
  | cons (instr : Assembly.Instr) (rest : Assembly.Program)
      (sourcePc compactPc compactSize : Nat)
      (code : List Located) (blocks : List SourceBlock)
      (hSize : sourceInstrSize? branchWidth instr = some compactSize)
      (hCode :
        emitSourceBlock? branchWidth compactPc table instr = some code)
      (hRest : BlocksValidFrom branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + compactSize) blocks) :
      BlocksValidFrom branchWidth table (instr :: rest) sourcePc compactPc
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: blocks)

theorem emitBlocksFrom?_valid
    {branchWidth : Nat} {table : LabelTable} :
    forall {source : Assembly.Program} {sourcePc compactPc : Nat}
      {blocks : List SourceBlock},
      emitBlocksFrom? branchWidth table source sourcePc compactPc =
          some blocks ->
        BlocksValidFrom branchWidth table source sourcePc compactPc blocks := by
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
      cases hSize : sourceInstrSize? branchWidth instr with
      | none => simp [hSize] at hEmit
      | some compactSize =>
          simp [hSize] at hEmit
          cases hCode :
              emitSourceBlock? branchWidth compactPc table instr with
          | none => simp [hCode] at hEmit
          | some code =>
              simp [hCode] at hEmit
              cases hRest :
                  emitBlocksFrom? branchWidth table rest
                    (sourcePc + instr.byteSize)
                    (compactPc + compactSize) with
              | none => simp [hRest] at hEmit
              | some restBlocks =>
                  simp [hRest] at hEmit
                  subst blocks
                  exact .cons instr rest sourcePc compactPc compactSize
                    code restBlocks hSize hCode (ih hRest)

theorem emitBlocks?_valid
    {source : Assembly.Program} {branchWidth : Nat} {table : LabelTable}
    {blocks : List SourceBlock}
    (hEmit : emitBlocks? source branchWidth table = some blocks) :
    BlocksValidFrom branchWidth table source 0 0 blocks := by
  exact emitBlocksFrom?_valid hEmit

theorem emitSourceBlock?_codeByteLength
    {branchWidth compactPc compactSize : Nat} {table : LabelTable}
    {instr : Assembly.Instr} {code : List Located}
    (hSize : sourceInstrSize? branchWidth instr = some compactSize)
    (hCode : emitSourceBlock? branchWidth compactPc table instr = some code) :
    Program.codeByteLength code = compactSize := by
  cases instr with
  | label name | prim name =>
      simp [sourceInstrSize?, emitSourceBlock?, emitInstrRev?] at hSize hCode
      subst compactSize
      subst code
      rfl
  | push value =>
      cases hWidth : widthForWord? value with
      | none => simp [sourceInstrSize?, hWidth] at hSize
      | some width =>
          simp [sourceInstrSize?, hWidth, emitSourceBlock?, emitInstrRev?]
            at hSize hCode
          subst compactSize
          subst code
          rfl
  | jump target | jumpi target =>
      cases hDest : lookupLabel? table target with
      | none => simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some dest =>
          by_cases hFits : fitsWidth? branchWidth dest = true
          · simp [sourceInstrSize?, emitSourceBlock?, emitInstrRev?,
              hDest, hFits] at hSize hCode
            subst compactSize
            subst code
            simp [Program.codeByteLength, Instr.byteSize, Nat.add_assoc]
          · simp [emitSourceBlock?, emitInstrRev?, hDest, hFits] at hCode

def BoundaryPair (blocks : List SourceBlock)
    (sourceEnd compactEnd sourcePc compactPc : Nat) : Prop :=
  (∃ block,
    block ∈ blocks ∧ block.sourcePc = sourcePc ∧
      block.compactPc = compactPc) ∨
  (sourcePc = sourceEnd ∧ compactPc = compactEnd)

theorem BlocksValidFrom.next_boundary
    {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom branchWidth table source
      sourcePc compactPc blocks) :
    forall {block : SourceBlock}, block ∈ blocks ->
      ∀ {compactSize : Nat},
        sourceInstrSize? branchWidth block.sourceInstr = some compactSize ->
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
    {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {blocks : List SourceBlock}
    (hValid : BlocksValidFrom branchWidth table source 0 0 blocks) :
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
    {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom branchWidth table source
      sourcePc compactPc blocks) :
    forall {block : SourceBlock}, block ∈ blocks ->
      ∃ compactSize,
        sourceInstrSize? branchWidth block.sourceInstr = some compactSize ∧
          emitSourceBlock? branchWidth block.compactPc table
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
    {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid : BlocksValidFrom branchWidth table source
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

theorem BlocksValidFrom.block_of_instrAtPcFrom
    {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {sourcePc compactPc query pc : Nat}
    {blocks : List SourceBlock} {instr : Assembly.Instr}
    (hValid : BlocksValidFrom branchWidth table source
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
    {branchWidth : Nat} {table : LabelTable}
    {source : Assembly.Program} {blocks : List SourceBlock}
    {query pc : Nat} {instr : Assembly.Instr}
    (hValid : BlocksValidFrom branchWidth table source 0 0 blocks)
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
  let blocks <- emitBlocks? physicalSource branchWidth labels
  if blocksCode blocks = program.code then
    if labelsConsistent? blocks labels then
      if program.wellFormed? then
        some
          { physicalSource := physicalSource
            branchWidth := branchWidth
            labels := labels
            codeLength := codeLength
            blocks := blocks
            program := program
            bytes := encode program }
      else
        none
    else
      none
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
  blocks : emitBlocks? artifact.physicalSource artifact.branchWidth
    artifact.labels = some artifact.blocks
  blockCode : blocksCode artifact.blocks = artifact.program.code
  labelsConsistent : LabelsConsistent artifact.blocks artifact.labels
  wellFormed : artifact.program.Valid ∧
    Program.codeLayoutFrom artifact.program.code 0 ∧
      Program.codeByteLength artifact.program.code < 18446744073709551616 ∧
        artifact.program.PCIndependent
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
                  cases hBlocks :
                      emitBlocks? physicalSource branchWidth labels with
                  | none => simp [hBlocks] at hCompile
                  | some blocks =>
                      simp [hBlocks] at hCompile
                      by_cases hCode : blocksCode blocks = program.code
                      · simp [hCode] at hCompile
                        by_cases hLabels :
                            labelsConsistent? blocks labels = true
                        · simp [hLabels] at hCompile
                          by_cases hWellFormed : program.wellFormed? = true
                          · simp [hWellFormed] at hCompile
                            cases hCompile
                            exact
                              Artifact.ValidFor.mk hPhysical.symm hWidth hLayout
                                hEmit hBlocks hCode
                                (labelsConsistent_of_check hLabels)
                                (Program.wellFormed_of_check hWellFormed) rfl
                          · simp [hWellFormed] at hCompile
                        · simp [hLabels] at hCompile
                      · simp [hCode] at hCompile

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
    {source : Assembly.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    DecodingCorrect artifact.program artifact.bytes := by
  have hValid := compile?_valid hCompile
  rw [hValid.bytes]
  exact
    decodingCorrectOfWellFormed
      hValid.wellFormed.1 hValid.wellFormed.2.1 hValid.wellFormed.2.2.1

theorem compile?_blocksValid
    {source : Assembly.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    BlocksValidFrom artifact.branchWidth artifact.labels
      artifact.physicalSource 0 0 artifact.blocks := by
  exact emitBlocks?_valid (compile?_valid hCompile).blocks

theorem compile?_block_of_instrAtPc
    {source : Assembly.Program} {artifact : Artifact}
    {query pc : Nat} {instr : Assembly.Instr}
    (hCompile : compile? source = some artifact)
    (hAt : artifact.physicalSource.instrAtPc query = some (pc, instr)) :
    ∃ block compactSize,
      block ∈ artifact.blocks ∧
        block.sourcePc = pc ∧ block.sourceInstr = instr ∧
          sourceInstrSize? artifact.branchWidth block.sourceInstr =
            some compactSize ∧
          emitSourceBlock? artifact.branchWidth block.compactPc
            artifact.labels block.sourceInstr = some block.code := by
  have hBlocks := compile?_blocksValid hCompile
  obtain ⟨block, hMem, hBlockPc, hInstr⟩ :=
    hBlocks.block_of_instrAtPc hAt
  obtain ⟨compactSize, hSize, hCode⟩ :=
    hBlocks.block_emit_of_mem hMem
  exact
    ⟨block, compactSize, hMem, hBlockPc, hInstr, hSize, hCode⟩

theorem compile?_initial_boundary
    {source : Assembly.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    BoundaryPair artifact.blocks artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code) 0 0 := by
  have hArtifact := compile?_valid hCompile
  have hBoundary := (compile?_blocksValid hCompile).initial_boundary
  rw [hArtifact.blockCode] at hBoundary
  exact hBoundary

theorem compile?_label_boundary
    {source : Assembly.Program} {artifact : Artifact}
    {label : Label} {sourceDest compactDest : Nat}
    (hCompile : compile? source = some artifact)
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

def BoundaryStateRel (artifact : Artifact)
    (target source : EVMState) : Prop :=
  ∃ sourcePc compactPc,
    BoundaryPair artifact.blocks artifact.physicalSource.byteLength
        (Program.codeByteLength artifact.program.code) sourcePc compactPc ∧
      source.pc = EvmYul.UInt256.ofNat sourcePc ∧
      target.pc = EvmYul.UInt256.ofNat compactPc ∧
      SameRuntimeData target source

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
    {target source : EVMState}
    (hBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      (sourcePc + sourceInstr.byteSize)
      (compactPc + compactInstr.byteSize))
    (hInstr : SimpleSourceInstrRel sourceInstr compactInstr)
    (hValid : compactInstr.Valid)
    (hIndependent : compactInstr.PCIndependent)
    (hDecode : decodeAt artifact.bytes compactPc compactInstr)
    (hPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hRel : SameRuntimeData target source) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      (openRunNResult artifact.bytes 1 target)
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
    {label : Label} {targetState sourceState : EVMState}
    (hBoundary : BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Program.codeByteLength artifact.program.code)
      sourceDest compactDest)
    (hSourceDest : artifact.physicalSource.labelPc label = some sourceDest)
    (hFits : FitsWidth width (EvmYul.UInt256.ofNat compactDest).toNat)
    (hPushDecode : decodeAt artifact.bytes compactPc
      (.push width (EvmYul.UInt256.ofNat compactDest)))
    (hJumpDecode : decodeAt artifact.bytes (compactPc + width + 1) .jump)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat compactPc)
    (hRel : SameRuntimeData targetState sourceState) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      (openRunNResult artifact.bytes 2 targetState)
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
    {label : Label} {targetState sourceState : EVMState}
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
    (hPushDecode : decodeAt artifact.bytes compactPc
      (.push width (EvmYul.UInt256.ofNat compactDest)))
    (hJumpDecode : decodeAt artifact.bytes (compactPc + width + 1) .jumpi)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat compactPc)
    (hSourcePc : sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hRel : SameRuntimeData targetState sourceState) :
    Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
      (openRunNResult artifact.bytes 2 targetState)
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
    {source : Assembly.Program} {artifact : Artifact}
    {block : SourceBlock} {targetState sourceState : EVMState}
    (hCompile : compile? source = some artifact)
    (hAccepted : Assembly.Accepted artifact.physicalSource)
    (hBlock : block ∈ artifact.blocks)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hSourcePc : sourceState.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : SameRuntimeData targetState sourceState) :
    ∃ targetFuel,
      Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
        (openRunNResult artifact.bytes targetFuel targetState)
        (Assembly.InteractionSemantics.Source.openStepAtResult
          artifact.physicalSource block.sourcePc block.sourceInstr
          sourceState) := by
  have hArtifact := compile?_valid hCompile
  have hBlocks := compile?_blocksValid hCompile
  have hDecoding := compile?_decodingCorrect hCompile
  obtain ⟨compactSize, hSize, hCode⟩ :=
    hBlocks.block_emit_of_mem hBlock
  have hNextBoundary := hBlocks.next_boundary hBlock hSize
  rw [(compile?_valid hCompile).blockCode] at hNextBoundary
  have hSourceMem : block.sourceInstr ∈ artifact.physicalSource :=
    hBlocks.sourceInstr_mem_of_block_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  cases sourceInstr with
  | label name =>
      simp [sourceInstrSize?, emitSourceBlock?, emitInstrRev?] at hSize hCode
      subst compactSize
      subst code
      let located : Located := { pc := compactPc, instr := .jumpdest }
      have hMem : located ∈ artifact.program.code :=
        hArtifact.mem_program_of_mem_block hBlock (by simp [located])
      exact
        ⟨1, openRunNResult_one_source_boundary_rel
          (sourcePc := sourcePc) (compactPc := compactPc)
          (sourceInstr := .label name) (compactInstr := .jumpdest)
          (by simpa using hNextBoundary)
          (SimpleSourceInstrRel.label name) trivial
          ((List.forall_iff_forall_mem.mp
            hArtifact.wellFormed.2.2.2) located hMem)
          (hDecoding.decodes located hMem) hTargetPc hSourcePc hRel⟩
  | prim op =>
      simp [sourceInstrSize?, emitSourceBlock?, emitInstrRev?] at hSize hCode
      subst compactSize
      subst code
      let located : Located := { pc := compactPc, instr := .prim op }
      have hMem : located ∈ artifact.program.code :=
        hArtifact.mem_program_of_mem_block hBlock (by simp [located])
      exact
        ⟨1, openRunNResult_one_source_boundary_rel
          (sourcePc := sourcePc) (compactPc := compactPc)
          (sourceInstr := .prim op) (compactInstr := .prim op)
          (by simpa using hNextBoundary)
          (SimpleSourceInstrRel.prim op) trivial
          ((List.forall_iff_forall_mem.mp
            hArtifact.wellFormed.2.2.2) located hMem)
          (hDecoding.decodes located hMem) hTargetPc hSourcePc hRel⟩
  | push value =>
      cases hWidth : widthForWord? value with
      | none => simp [sourceInstrSize?, hWidth] at hSize
      | some width =>
          simp [sourceInstrSize?, hWidth, emitSourceBlock?, emitInstrRev?]
            at hSize hCode
          subst compactSize
          subst code
          let located : Located :=
            { pc := compactPc, instr := .push width value }
          have hMem : located ∈ artifact.program.code :=
            hArtifact.mem_program_of_mem_block hBlock (by simp [located])
          exact
            ⟨1, openRunNResult_one_source_boundary_rel
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
  | jump target =>
      cases hDest : lookupLabel? artifact.labels target with
      | none =>
          simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some compactDest =>
          by_cases hFitsBool :
              fitsWidth? artifact.branchWidth compactDest = true
          · simp [sourceInstrSize?, emitSourceBlock?, emitInstrRev?,
              hDest, hFitsBool] at hSize hCode
            subst compactSize
            subst code
            obtain ⟨sourceDest, hSourceDest⟩ :=
              Assembly.Program.target_resolves_of_accepted
                (instr := .jump target) (target := target)
                hAccepted.checked (by simpa using hSourceMem)
                (by simp [Assembly.Instr.targets])
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
              ⟨2, openRunNResult_push_jump_source_boundary_rel
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
          · simp [sourceInstrSize?, emitSourceBlock?, emitInstrRev?,
              hDest, hFitsBool] at hSize hCode
            subst compactSize
            subst code
            obtain ⟨sourceDest, hSourceDest⟩ :=
              Assembly.Program.target_resolves_of_accepted
                (instr := .jumpi target) (target := target)
                hAccepted.checked (by simpa using hSourceMem)
                (by simp [Assembly.Instr.targets])
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
              ⟨2, openRunNResult_push_jumpi_source_boundary_rel
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

end InteractionSemantics

end Compact
end Assembly
end EvmCompiler
