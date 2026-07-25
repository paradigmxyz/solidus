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
  | scratchBase
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

/--
The reserved binder name that retags a slot as an anonymous `.word` instead of
a named `.local`.

Real binder names are Yul identifiers or compiler-generated temporaries, all of
which are non-empty, so the empty string is unambiguous.  It gives the
compiler-owned zero-byte `bindLocals` pseudo-instruction a way to say "this
slot is now an anonymous word" — the classification a procedure's return values
need at procedure exit, where `Shape.procExit` demands `.word` slots.  Getting
this wrong can only make a compile-time shape check *fail* (fail-closed): slot
tags are never read by any semantics function, and the only semantic content of
a `Shape` is its length (`StackRealizes shape state := shape.length ≤
state.stack.length`) together with `returnTokenDepth?`.
-/
def anonymousBinder : String := ""

/-- Interpret a `bindLocals` binder name as a slot tag: the reserved
`anonymousBinder` produces an anonymous `.word`, every other name produces the
corresponding `.local`. -/
def slotOfBinder (name : String) : Slot :=
  if name = anonymousBinder then .word else .local name

@[simp] theorem slotOfBinder_anonymousBinder :
    slotOfBinder anonymousBinder = .word := by
  simp [slotOfBinder]

theorem slotOfBinder_of_ne {name : String} (h : name ≠ anonymousBinder) :
    slotOfBinder name = .local name := by
  simp [slotOfBinder, h]

@[simp] theorem slotOfBinder_replicate (count : Nat) :
    (List.replicate count anonymousBinder).map slotOfBinder =
      List.replicate count Slot.word := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

def bindLocals? (offset : Nat) (names : List String)
    (shape : Shape) : Option Shape :=
  if offset + names.length ≤ shape.length then
    some
      { shape with
        slots :=
          shape.slots.take offset ++ names.map slotOfBinder ++
            shape.slots.drop (offset + names.length) }
  else
    none

def bindScratch? (baseDepth : Nat) (shape : Shape) : Option Shape :=
  match shape.slots[baseDepth]? with
  | none => none
  | some _ =>
      some
        { shape with
          slots := shape.slots.set baseDepth .scratchBase }

def hasPrefix (prefixShape shape : Shape) : Prop :=
  prefixShape.tail = shape.tail ∧
    ∃ suffix, shape.slots = prefixShape.slots ++ suffix

def slotsAgree : List Slot → List Slot → Bool
  | [], _ => true
  | _, [] => true
  | .returnPC _ :: leftRest, .returnToken :: rightRest =>
      slotsAgree leftRest rightRest
  | .returnToken :: leftRest, .returnPC _ :: rightRest =>
      slotsAgree leftRest rightRest
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
  | bindLocals (offset : Nat) (names : List String)
  | bindScratch (baseDepth : Nat) (name : String) (slot : Nat)
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
