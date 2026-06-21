import EvmCompiler.Assembly.Bytecode

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

theorem byteSize_pos (instr : Instr) : 0 < instr.byteSize := by
  cases instr <;> simp [byteSize]

end Instr

structure Located where
  pc : Nat
  instr : Instr
  deriving DecidableEq, Repr

structure Program where
  code : List Located
  deriving DecidableEq, Repr

namespace Program

def fetch (program : Program) (pc : Nat) : Option Instr :=
  (program.code.find? fun located => located.pc == pc).map Located.instr

def byteLength (program : Program) : Nat :=
  program.code.foldl
    (fun total located => total + located.instr.byteSize) 0

def Valid (program : Program) : Prop :=
  program.code.Forall fun located => located.instr.Valid

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

def encodeInstr : Instr -> List UInt8
  | .push width value => encodePush width value
  | .jump => Bytecode.encodeInstr .jump
  | .jumpi => Bytecode.encodeInstr .jumpi
  | .jumpdest => Bytecode.encodeInstr .jumpdest
  | .prim op => Bytecode.encodeInstr (.prim op)

def encodeLocated (located : Located) : List UInt8 :=
  encodeInstr located.instr

def encode (program : Program) : ByteArray :=
  Bytecode.ofList (program.code.flatMap encodeLocated)

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
  some
    { physicalSource := physicalSource
      branchWidth := branchWidth
      labels := labels
      codeLength := codeLength
      program := program
      bytes := encode program }

structure Artifact.ValidFor (artifact : Artifact)
    (source : Assembly.Program) : Prop where
  physicalSource : artifact.physicalSource = prepare source
  branchWidth : widthForNat? artifact.physicalSource.byteLength =
    some artifact.branchWidth
  layout : layout? artifact.physicalSource artifact.branchWidth =
    some (artifact.labels, artifact.codeLength)
  emitted : emit? artifact.physicalSource artifact.branchWidth artifact.labels =
    some artifact.program
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
                  cases hCompile
                  exact
                    Artifact.ValidFor.mk hPhysical.symm hWidth hLayout hEmit rfl

end Compact
end Assembly
end EvmCompiler
