import EvmYul.UInt256

namespace EvmCompiler

abbrev Word := EvmYul.UInt256

namespace MemoryContract

def wordBytes : Nat :=
  32

/--
Default private-memory capacity used by the standard Solidity import route.

One word is reserved for allocator metadata; the remaining 8192 words match
the current maximum scratch-frame planning budget.
-/
def defaultReservedWords : Nat :=
  8193

/--
A byte interval that the source promises to leave available to the compiler.

The interval is half-open: `[base, endExclusive)`. `memoryguard(size)` gives
the compiler the interval beginning at `size`; the value returned to source
code is `endExclusive`, so ordinary source allocation starts after it.
-/
structure ScratchReservation where
  base : Nat
  words : Nat
  deriving DecidableEq, Inhabited, Repr

namespace ScratchReservation

def bytes (reservation : ScratchReservation) : Nat :=
  wordBytes * reservation.words

def endExclusive (reservation : ScratchReservation) : Nat :=
  reservation.base + reservation.bytes

def allocatorCell (reservation : ScratchReservation) : Nat :=
  reservation.base

def frameBase (reservation : ScratchReservation) : Nat :=
  reservation.base + wordBytes

def usableWords (reservation : ScratchReservation) : Nat :=
  reservation.words - 1

def WellFormed (reservation : ScratchReservation) : Prop :=
  reservation.base % wordBytes = 0 ∧
    reservation.endExclusive < EvmYul.UInt256.size

def HostAddressable (reservation : ScratchReservation) : Prop :=
  reservation.endExclusive < USize.size

instance wellFormedDecidable (reservation : ScratchReservation) :
    Decidable reservation.WellFormed := by
  unfold WellFormed
  infer_instance

instance hostAddressableDecidable (reservation : ScratchReservation) :
    Decidable reservation.HostAddressable := by
  unfold HostAddressable
  infer_instance

def wellFormed? (reservation : ScratchReservation) : Bool :=
  decide reservation.WellFormed

def containsByte (reservation : ScratchReservation) (address : Nat) : Prop :=
  reservation.base ≤ address ∧ address < reservation.endExclusive

def containsRegion (reservation : ScratchReservation)
    (base words : Nat) : Prop :=
  reservation.base ≤ base ∧
    base + wordBytes * words ≤ reservation.endExclusive

instance containsRegionDecidable (reservation : ScratchReservation)
    (base words : Nat) : Decidable (reservation.containsRegion base words) := by
  unfold containsRegion
  infer_instance

def sourceAccessAllowed (reservation : ScratchReservation)
    (address size : Nat) : Prop :=
  address + size ≤ reservation.base ∨
    reservation.endExclusive ≤ address

instance sourceAccessAllowedDecidable (reservation : ScratchReservation)
    (address size : Nat) :
    Decidable (reservation.sourceAccessAllowed address size) := by
  unfold sourceAccessAllowed
  infer_instance

def returnedPointer (reservation : ScratchReservation) : Word :=
  EvmYul.UInt256.ofNat reservation.endExclusive

end ScratchReservation

/--
Source-facing memory ownership supplied before allocation.

`none` is unrestricted Yul memory and authorizes only stack allocation.
`some reservation` records a trusted `memoryguard`-style promise that source
memory accesses stay outside the reserved interval.
-/
structure Contract where
  scratch? : Option ScratchReservation := none
  deriving DecidableEq, Inhabited, Repr

def unrestricted : Contract :=
  {}

def ofMemoryGuard? (size : Word) (reservedWords : Nat) :
    Option Contract :=
  let reservation : ScratchReservation :=
    { base := size.toNat, words := reservedWords }
  if reservation.wellFormed? then
    some { scratch? := some reservation }
  else
    none

def returnedPointer? (contract : Contract) : Option Word :=
  contract.scratch?.map ScratchReservation.returnedPointer

def authorizesRegion (contract : Contract) (base words : Nat) : Prop :=
  ∃ reservation,
    contract.scratch? = some reservation ∧
      reservation.containsRegion base words

instance authorizesRegionDecidable (contract : Contract)
    (base words : Nat) :
    Decidable (authorizesRegion contract base words) := by
  unfold authorizesRegion
  cases hReservation : contract.scratch? with
  | none =>
      exact isFalse (by simp [hReservation])
  | some reservation =>
      simp [hReservation]
      infer_instance

end MemoryContract
end EvmCompiler
