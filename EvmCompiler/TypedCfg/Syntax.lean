import EvmCompiler.Assembly.Syntax

namespace EvmCompiler
namespace TypedCfg

abbrev Word := Assembly.Word
abbrev Label := Assembly.Label

/--
Symbolic stack slots used by the typed CFG.

The slots are proof-level names for stack positions. They are not runtime
values. A later lowering pass chooses concrete DUP/SWAP/POP/PUSH code that
realizes these symbolic slots on the EVM stack.
-/
inductive Slot where
  | word
  | literal (value : Word)
  | local (name : String)
  | temp (scope : Nat) (index : Nat)
  | returnToken
  | returnPC (site : Nat)
  | returnValue (name : String) (index : Nat)
  deriving DecidableEq, Repr

inductive FrameTail where
  | closed
  | caller
  deriving DecidableEq, Repr

/--
A symbolic stack prefix together with the part of the caller stack that the
current procedure is not allowed to inspect.

The opaque `caller` tail is the row variable for procedure typing: the same
procedure body is valid for callers with any hidden stack depth, while every
instruction must still find all operands in `slots`.
-/
structure Shape where
  slots : List Slot
  tail : FrameTail := .closed
  deriving DecidableEq, Repr

namespace Shape

def closed (slots : List Slot := []) : Shape :=
  { slots := slots, tail := .closed }

def caller (slots : List Slot := []) : Shape :=
  { slots := slots, tail := .caller }

instance : Coe (List Slot) Shape where
  coe := fun slots => closed slots

def length (shape : Shape) : Nat :=
  shape.slots.length

def get? (shape : Shape) (depth : Nat) : Option Slot :=
  shape.slots[depth]?

def erase (depth : Nat) (shape : Shape) : Shape :=
  { shape with slots := shape.slots.eraseIdx depth }

def pop (n : Nat) (shape : Shape) : Shape :=
  { shape with slots := shape.slots.drop n }

def pushWords (n : Nat) (shape : Shape) : Shape :=
  { shape with slots := List.replicate n Slot.word ++ shape.slots }

def hasPrefix (prefixShape shape : Shape) : Prop :=
  prefixShape.tail = shape.tail ∧
    ∃ suffix, shape.slots = prefixShape.slots ++ suffix

def slotsAgree : List Slot → List Slot → Bool
  | [], _ => true
  | _, [] => true
  | left :: leftRest, right :: rightRest =>
      (decide (left = .word) || decide (right = .word) ||
        decide (left = right)) &&
          slotsAgree leftRest rightRest

/--
Row-style stack compatibility. Closed rows must have exactly the same length.
An opaque caller row may instantiate to additional hidden slots, provided the
known prefixes agree.
-/
def compatible (left right : Shape) : Bool :=
  slotsAgree left.slots right.slots &&
    if left.length = right.length then
      true
    else if left.length < right.length then
      decide (left.tail = .caller)
    else
      decide (right.tail = .caller)

def relabelCompatible (left right : Shape) : Bool :=
  slotsAgree left.slots right.slots &&
    decide (left.length = right.length) &&
    decide (left.tail = right.tail)

def unwindTo (target current : Shape) : Option Shape :=
  if target.tail = current.tail ∧
      target.length ≤ current.length ∧
      current.slots.drop (current.length - target.length) = target.slots then
    some target
  else
    none

@[simp] theorem pushWords_zero (shape : Shape) :
    pushWords 0 shape = shape := by
  simp [pushWords]

@[simp] theorem pop_zero (shape : Shape) :
    pop 0 shape = shape := by
  cases shape
  simp [pop]

end Shape

structure ReturnSite where
  token : Word
  target : Label
  caseLabel : Label
  deriving DecidableEq, Repr

/--
Primitive instructions in the typed CFG.

Control flow is deliberately not represented by raw `JUMP`/`JUMPI` here.
Transfers are terminators whose targets have declared stack shapes.
-/
inductive Instr where
  | push (value : Word)
  | returnToken (value : Word)
  | prim (op : Assembly.PrimOp)
  | pop
  | dup (depth : Nat)
  | swap (depth : Nat)
  | relabel (target : Shape)
  | unwind (target : Shape)
  deriving DecidableEq, Repr

inductive Terminator where
  | fallthrough (next : Label)
  | jump (target : Label)
  | jumpi (target : Label) (fallthrough : Label)
  | returnDispatch (returnCount : Nat) (sites : List ReturnSite)
  | halt (kind : Assembly.HaltKind)
  | invalid
  deriving DecidableEq, Repr

structure Block where
  label : Label
  input : Shape
  body : List Instr
  output : Shape
  term : Terminator
  deriving DecidableEq, Repr

structure Program where
  entry : Label
  blocks : List Block
  deriving DecidableEq, Repr

namespace Program

def findBlock? (program : Program) (label : Label) : Option Block :=
  program.blocks.find? (fun block => block.label == label)

def labelShape? (program : Program) (label : Label) : Option Shape :=
  (program.findBlock? label).map (fun block => block.input)

def extractBlock? : List Block → Label → Option (Block × List Block)
  | [], _ => none
  | block :: rest, label =>
      if block.label = label then
        some (block, rest)
      else do
        let (entry, remaining) ← extractBlock? rest label
        some (entry, block :: remaining)

def blocksInLoweringOrder? (program : Program) : Option (List Block) := do
  let (entry, remaining) ← extractBlock? program.blocks program.entry
  some (entry :: remaining)

end Program

end TypedCfg
end EvmCompiler
