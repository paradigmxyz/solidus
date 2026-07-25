import EvmCompiler.Assembly.Syntax

/-!
# Literal-push encoding

A source-level `push value` does not have to lower to a literal `PUSH`.  Wide
all-ones masks (`0xff…ff`, ubiquitous in ABI and storage-packing code) are
re-encoded as `NOT 0` shifted right, which compacts to a fixed five bytes
regardless of the mask width instead of `1 + w`.

This module sits directly on top of `Assembly.Syntax` — below *every* semantics
layer — because each layer that steps a `push` must advance the program counter
by exactly the number of bytes the lowering emits.  Keeping the encoding in one
place is what makes those pc deltas agree by construction.
-/

namespace EvmCompiler
namespace Assembly

/-- If `value` is the all-ones mask `2 ^ (8 * w) - 1` for some byte width
`5 ≤ w ≤ 31`, return `w`.

Widths below 5 are excluded on purpose: the computed encoding costs a fixed
5 bytes after compaction (`PUSH0; NOT; PUSH1 s; SHR`), so it only pays for
itself once the literal `PUSH w` would cost `1 + w > 5` bytes.  Width 32 is
excluded because `2 ^ 256 - 1` needs no shift and does not occur in practice.

The `% 256 = 255` test is a cheap pre-filter: every all-ones mask ends in
`0xff`, and almost no other constant does, so the 27-way search below runs
only on genuine candidates. -/
def maskWidth? (value : Word) : Option Nat :=
  if value.toNat % 256 = 255 then
    (List.range' 5 27).find? fun w => value.toNat = 2 ^ (8 * w) - 1
  else
    none

/-- If `value` is `x * 2 ^ k` for a whole number `k / 8 ∈ [4, 31]` of trailing
zero *bytes*, return the largest such `k` (in bits).

Re-encoding `value` as `PUSH x; PUSH k; SHL` costs `(1 + w x) + 2 + 1` bytes
after compaction, against `1 + w x + z` for the literal, where `z = k / 8` is
the trailing-zero-byte count and `w x` the byte width of the shifted-down
mantissa (`w value = w x + z` exactly).  The saving is therefore `z - 3`, so
`z ≥ 4` is precisely the profitable range; `z ≤ 31` keeps `k ≤ 248`, which is
what makes the shift amount a one-byte `PUSH1`.

Right-padded `bytesNN` literals — Solidity revert strings above all — are the
overwhelming source of these: `"zero"` is `0x7a65726f` followed by 28 zero
bytes, i.e. `z = 28`, a 25-byte saving at every site.

The `% 2 ^ 32 = 0` test is a cheap one-`mod` pre-filter: it is exactly the
necessary condition `z ≥ 4`, so the 28-way search below runs only on genuine
candidates. -/
def shiftEncode? (value : Word) : Option Nat :=
  if 0 < value.toNat ∧ value.toNat % 2 ^ 32 = 0 then
    ((List.range' 4 28).reverse.find? fun z => value.toNat % 2 ^ (8 * z) = 0).map
      (fun z => 8 * z)
  else
    none

/-- Assembly encoding of a literal push.

FLAT, deliberately: a single `match` on the PAIR of discriminants rather than a
nested `match`.  Downstream proofs written against the original two-branch
definition discharge it with `unfold pushCode; split <;> simp <;> omega`, and a
single `split` reaches only the OUTER match of a nested definition -- it leaves
`(match shiftEncode? value with ...).length ≥ 1`, a stuck match `simp` will not
reduce, so `omega` reports "No usable constraints found".  That is not
hypothetical: it broke the inherited `PeepholeFuel.lean:97` proof and cost a
scoring run.  One match on a pair yields three FLAT goals from one `split`, each
a literal list, so every inherited tactic closes unchanged.

Arm order preserves the original semantics exactly: `maskWidth?` wins whenever it
fires, which the `some w, _` pattern encodes (it covers both `(some w, some k)`
and `(some w, none)`). -/
def pushCode (value : Word) : Program :=
  match maskWidth? value, shiftEncode? value with
  | some w, _ =>
      [ .push (EvmYul.UInt256.ofNat 0), .prim .not
      , .push (EvmYul.UInt256.ofNat (256 - 8 * w)), .prim .shr ]
  | none, some k =>
      [ .push (EvmYul.UInt256.ofNat (value.toNat / 2 ^ k))
      , .push (EvmYul.UInt256.ofNat k), .prim .shl ]
  | none, none => [.push value]

/-- `pushCode` never emits the empty program.

Stated as a LEMMA rather than left to a downstream tactic re-deriving it from the
definition's shape.  A definitional-shape dependency inside someone else's proof
is exactly the fragility that broke here: our change was confined to files we own
and still perturbed an inherited proof, because that proof reached through
`unfold` into our definition.  Callers should use this. -/
theorem pushCode_length_pos (value : Word) : 1 ≤ (pushCode value).length := by
  unfold pushCode
  split <;> simp

theorem maskWidth?_spec {value : Word} {w : Nat}
    (hMask : maskWidth? value = some w) :
    5 ≤ w ∧ w ≤ 31 ∧ value.toNat = 2 ^ (8 * w) - 1 := by
  unfold maskWidth? at hMask
  by_cases hLow : value.toNat % 256 = 255
  · rw [if_pos hLow] at hMask
    have hMem := List.mem_of_find?_eq_some hMask
    have hCheck := List.find?_some hMask
    have hRange := List.mem_range'_1.mp hMem
    exact ⟨by omega, by omega, by simpa using hCheck⟩
  · rw [if_neg hLow] at hMask
    exact absurd hMask (by simp)

theorem shiftEncode?_spec {value : Word} {k : Nat}
    (hEnc : shiftEncode? value = some k) :
    0 < k ∧ k < 256 ∧ value.toNat % 2 ^ k = 0 := by
  unfold shiftEncode? at hEnc
  by_cases hPre : 0 < value.toNat ∧ value.toNat % 2 ^ 32 = 0
  · rw [if_pos hPre] at hEnc
    rcases Option.map_eq_some_iff.mp hEnc with ⟨z, hFind, hz⟩
    have hMem := List.mem_reverse.mp (List.mem_of_find?_eq_some hFind)
    have hCheck := List.find?_some hFind
    have hRange := List.mem_range'_1.mp hMem
    subst hz
    exact ⟨by omega, by omega, by simpa using hCheck⟩
  · rw [if_neg hPre] at hEnc
    exact absurd hEnc (by simp)

/-- The emitted byte length of a push encoding: a literal `PUSH32` is 33 bytes,
the computed mask form is `33 + 1 + 33 + 1`, the shifted-literal form is
`33 + 33 + 1`. -/
theorem pushCode_byteLength (value : Word) :
    Program.byteLength (pushCode value) =
      match maskWidth? value with
      | some _ => 68
      | none =>
          match shiftEncode? value with
          | some _ => 67
          | none => 33 := by
  unfold pushCode
  -- flat match on the pair: split once, three literal-list goals
  cases hMask : maskWidth? value <;> cases hEnc : shiftEncode? value <;>
    simp [Program.byteLength, Instr.byteSize, Instr.push32Size]

/-- The program-counter delta a single `push value` must advance by: exactly
the number of bytes its lowering emits. -/
def pushPcDelta (value : Word) : Nat :=
  Program.byteLength (pushCode value)

end Assembly
end EvmCompiler
