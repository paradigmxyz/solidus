import EvmCompiler.Objects.SourceAccepted
import EvmCompiler.Functions.Compiler
import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Objects

/-
Backend object/data layout support.

Yul object builtins are compile-time names for locations in the final code
image.  The executable code for an object is followed by payload bytes for
child objects and data sects; `dataoffset` names the start of one payload
chunk, `datasize` names its byte length, and Yul-level `datacopy` lowers to
ordinary EVM `codecopy` over this image.

This module keeps that layout computation at the object boundary.  The
source-facing object interpreter is still a transparent wrapper over root code;
the layout/image relation is backend evidence used by object/data builtin
lowering and the bytecode-image lane.
-/

namespace Name

def containsDot (name : Name) : Bool :=
  name.toList.contains '.'

def objectPathComponent? (name : Name) : Bool :=
  !containsDot name

end Name

namespace DataSection

def byteLength (sect : DataSection) : Nat :=
  sect.bytes.length

def size (sect : DataSection) : Word :=
  EvmYul.UInt256.ofNat sect.byteLength

def namedSizeEntry? (sect : DataSection) : Option (Name × Word) :=
  match sect.name? with
  | some name =>
      if Name.objectPathComponent? name then
        some (name, sect.size)
      else
        none
  | none => none

def namedOffsetEntryFromNat? (base : Nat) (sect : DataSection) :
    Option (Name × Word) :=
  match sect.name? with
  | some name =>
      if Name.objectPathComponent? name then
        some (name, EvmYul.UInt256.ofNat base)
      else
        none
  | none => none

namespace Sections

def payloadBytes : List DataSection → List UInt8
  | [] => []
  | sect :: rest => sect.bytes ++ payloadBytes rest

def byteLength (sects : List DataSection) : Nat :=
  (payloadBytes sects).length

def namedSizeEntries : List DataSection → List (Name × Word)
  | [] => []
  | sect :: rest =>
      match sect.namedSizeEntry? with
      | some entry => entry :: namedSizeEntries rest
      | none => namedSizeEntries rest

def namedOffsetEntriesFromNat : Nat → List DataSection → List (Name × Word)
  | _, [] => []
  | base, sect :: rest =>
      let tail :=
        namedOffsetEntriesFromNat (base + sect.byteLength) rest
      match sect.namedOffsetEntryFromNat? base with
      | some entry => entry :: tail
      | none => tail

theorem payloadBytes_nil :
    payloadBytes [] = [] := rfl

theorem byteLength_nil :
    byteLength [] = 0 := by rfl

theorem payloadBytes_cons (sect : DataSection)
    (sects : List DataSection) :
    payloadBytes (sect :: sects) =
      sect.bytes ++ payloadBytes sects := rfl

theorem byteLength_cons (sect : DataSection)
    (sects : List DataSection) :
    byteLength (sect :: sects) =
      sect.byteLength + byteLength sects := by
  simp [byteLength, payloadBytes, DataSection.byteLength]

end Sections
end DataSection

namespace ObjectLayout

structure Entry where
  name : Name
  offset : Word
  size : Word
  deriving Inhabited, Repr

structure Layout where
  entries : List Entry
  deriving Inhabited, Repr

def findEntry? (layout : Layout) (name : Name) : Option Entry :=
  layout.entries.find? fun entry => entry.name == name

def offset? (layout : Layout) (name : Name) : Option Word := do
  let entry ← findEntry? layout name
  some entry.offset

def size? (layout : Layout) (name : Name) : Option Word := do
  let entry ← findEntry? layout name
  some entry.size

end ObjectLayout

namespace Object

def codeTarget? (object : Object) : Option Assembly.TargetProgram :=
  Functions.Inline.Program.compile? object.code

def codeBytes? (object : Object) : Option (List UInt8) := do
  let target ← codeTarget? object
  some (Assembly.Bytecode.encodeTarget target).toList

mutual
  def imageBytesFuel? : Nat → Object → Option (List UInt8)
    | 0, _object => none
    | fuel + 1, object => do
        let code ← codeBytes? object
        let childPayload ← ObjectList.imageBytesFuel? fuel object.objects
        some (code ++ childPayload ++
          DataSection.Sections.payloadBytes object.data)

  def ObjectList.imageBytesFuel? : Nat → List Object → Option (List UInt8)
    | 0, _objects => none
    | _fuel + 1, [] => some []
    | fuel + 1, object :: rest => do
        let head ← imageBytesFuel? fuel object
        let tail ← ObjectList.imageBytesFuel? fuel rest
        some (head ++ tail)
end

noncomputable def imageBytes? (object : Object) : Option (List UInt8) :=
  imageBytesFuel? (sizeOf object + 1) object

namespace ObjectList

noncomputable def imageBytes? (objects : List Object) : Option (List UInt8) :=
  imageBytesFuel? (sizeOf objects + 1) objects

end ObjectList

noncomputable def imageSize? (object : Object) : Option Word := do
  let image ← imageBytes? object
  some (EvmYul.UInt256.ofNat image.length)

def dataLayoutEntriesFromNat (base : Nat) (data : List DataSection) :
    List ObjectLayout.Entry :=
  DataSection.Sections.namedOffsetEntriesFromNat base data |>.map
    (fun (name, offset) =>
      { name := name
        offset := offset
        size := (data.find? (fun sect => sect.name? == some name))
          |>.map DataSection.size |>.getD (EvmYul.UInt256.ofNat 0) })

def ObjectList.layoutEntriesFromNatFuel? :
    Nat → Nat → List Object → Option (List ObjectLayout.Entry)
  | 0, _base, _objects => none
  | _fuel + 1, _base, [] => some []
  | fuel + 1, base, object :: rest => do
      let image ← Object.imageBytesFuel? fuel object
      let tail ←
        ObjectList.layoutEntriesFromNatFuel? fuel (base + image.length) rest
      some
        ({ name := object.name
           offset := EvmYul.UInt256.ofNat base
           size := EvmYul.UInt256.ofNat image.length } :: tail)

noncomputable def ObjectList.layoutEntriesFromNat? (base : Nat) (objects : List Object) :
    Option (List ObjectLayout.Entry) :=
  ObjectList.layoutEntriesFromNatFuel? (sizeOf objects + 1) base objects

noncomputable def payloadLayoutEntriesFromNat? (base : Nat) (objects : List Object)
    (data : List DataSection) : Option (List ObjectLayout.Entry) := do
  let objectEntries ← ObjectList.layoutEntriesFromNat? base objects
  let objectBytes ← ObjectList.imageBytes? objects
  let dataBase := base + objectBytes.length
  some (objectEntries ++ dataLayoutEntriesFromNat dataBase data)

noncomputable def payloadLayout? (object : Object) : Option ObjectLayout.Layout := do
  let code ← codeBytes? object
  let entries ←
    payloadLayoutEntriesFromNat? code.length object.objects object.data
  some { entries := entries }

end Object

namespace Program

noncomputable def bytecodeImage? (program : Program) : Option ByteArray := do
  let image ← Object.imageBytes? program.root
  some (Assembly.Bytecode.ofList image)

noncomputable def payloadLayout? (program : Program) : Option ObjectLayout.Layout :=
  Object.payloadLayout? program.root

end Program

end Objects
end EvmCompiler
