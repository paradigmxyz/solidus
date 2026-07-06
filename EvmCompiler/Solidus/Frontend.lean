import EvmYul.UInt256
import EvmCompiler.Core.MemoryContract

/-!
# Frozen frontend spec types (Solidus Arena freeze cone)

`EvmCompiler.Solidus.compile_correct` existentially quantifies over a
`Solidity.Frontend.ObjectBuiltinContext` and runs the frozen source semantics
against it. The witness type and the pure data types it is built from are
relocated here out of the mutable, 4.7k-line compiler frontend
`EvmCompiler/Solidity/Frontend.lean` so that an adversary cannot collapse the
context's shape to a trivial type while leaving the frozen hashes unchanged.

Only the pure data *types* move (`Name`, `Word`, `ObjectLayout`,
`ObjectLayout.Entry`, `ImmutableReference`, `ObjectBuiltinContext`); all
compiler methods and constructors on them stay mutable in the original file,
which now imports this module. Names and the `Solidity.Frontend` namespace are
preserved, so downstream references remain valid.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

abbrev Name := String
abbrev Word := EvmYul.UInt256

structure ObjectLayout.Entry where
  name : Name
  offset : Word
  size : Word
  deriving Inhabited, Repr

structure ObjectLayout where
  entries : List ObjectLayout.Entry
  deriving Inhabited, Repr

structure ImmutableReference where
  start : Nat
  length : Nat
  deriving Inhabited, Repr

/-- Existential builtin-resolution witness handed to the frozen source
semantics. Every field is pure data; `layout` and the association lists resolve
`datasize`/`dataoffset`/linker/immutable builtins, and `memoryContract`
records the (stack-only) memory policy. -/
structure ObjectBuiltinContext where
  layout : ObjectLayout
  dataSizes : List (Name × Word)
  dataOffsets : List (Name × Word)
  linkerSymbols : List (Name × Word)
  immutableValues : List (Name × Word) := []
  immutableReferences : List (Name × List ImmutableReference) := []
  selfSize? : Option (Name × Word) := none
  memoryContract : MemoryContract.Contract :=
    MemoryContract.unrestricted
  deriving Inhabited, Repr

end Frontend
end Solidity
end EvmCompiler
