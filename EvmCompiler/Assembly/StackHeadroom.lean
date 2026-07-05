import EvmCompiler.Assembly.Compact

/-!
# Per-pc exact stack-height certificate for compact artifacts

This module defines a decidable operand-stack-height certificate for compiled
`Compact.Artifact`s together with an executable validator (`check?`).

Design (stage 1, uniform-height fragment):

* the certificate is an exact height table keyed by physical program counter
  (as an EVM word), covering every reachable source-block boundary, generated
  branch midpoint, and the terminal sentinel;
* control flow is read off the compact block layout: every emitted branch is
  a `PUSH dest; JUMP(I)` pair whose destination comes from the compiled label
  table, so all edges are static;
* the table is validated block by block: each entry must agree exactly with
  the entry of every static successor, all entries are capped at `stackCap`,
  and the anchor `heights(0) = 0` matches a frame entered with an empty
  stack.

Programs whose shared procedure bodies execute at several different absolute
heights fail validation (fail-closed): the certificate producer returns
`none` and no headroom claim is made.  Extending the certificate to a
call-protocol-aware frame-relative form is staged work; the checker interface
below is deliberately independent of that extension.

Soundness against the gasful EVM semantics lives in
`EvmCompiler.Assembly.StackHeadroomSound`.
-/

namespace EvmCompiler
namespace Assembly
namespace StackHeadroom

/-- Exact operand-stack heights keyed by physical pc (as an EVM word). -/
abbrev HeightList := List (Word × Nat)

/-- The stack-headroom certificate: an exact per-pc height table. -/
structure Cert where
  heights : HeightList
  deriving Repr, DecidableEq

/-- The certified operand-stack capacity: one below the EVM limit, so that
every instruction (net stack effect at most `+1`) stays within `1024`. -/
def stackCap : Nat := 1023

def lookupHeight (heights : HeightList) (pc : Word) : Option Nat :=
  (heights.find? (fun entry => decide (entry.1 = pc))).map (·.2)

def heightsBounded? (heights : HeightList) : Bool :=
  heights.all (fun entry => decide (entry.2 ≤ stackCap))

/-- Per-block validation of the height table against the block's static
successors.  Blocks without a table entry are certified unreachable by the
surrounding rules and are skipped. -/
def blockOk? (artifact : Compact.Artifact) (heights : HeightList)
    (block : Compact.SourceBlock) : Bool :=
  match lookupHeight heights (EvmYul.UInt256.ofNat block.compactPc) with
  | none =>
      -- an entry-less (unreachable) branch block must not have a stray
      -- midpoint entry: the midpoint invariant is tied to the block entry.
      match block.sourceInstr with
      | .jump _ | .jumpi _ =>
          lookupHeight heights
              (EvmYul.UInt256.ofNat
                (block.compactPc + artifact.branchWidth + 1)) ==
            none
      | _ => true
  | some h =>
      match block.sourceInstr with
      | .label _ =>
          lookupHeight heights
              (EvmYul.UInt256.ofNat (block.compactPc + 1)) == some h
      | .push _ =>
          match Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
              artifact.branchWidth block.sourcePc block.sourceInstr with
          | some size =>
              lookupHeight heights
                  (EvmYul.UInt256.ofNat (block.compactPc + size)) ==
                some (h + 1)
          | none => false
      | .pushLabel _ => false
      | .jumpDynamic => false
      | .jump target =>
          match Compact.lookupLabel? artifact.labels target with
          | some dest =>
              (lookupHeight heights
                  (EvmYul.UInt256.ofNat
                    (block.compactPc + artifact.branchWidth + 1)) ==
                some (h + 1)) &&
                (lookupHeight heights (EvmYul.UInt256.ofNat dest) == some h)
          | none => false
      | .jumpi target =>
          match Compact.lookupLabel? artifact.labels target with
          | some dest =>
              decide (1 ≤ h) &&
                (lookupHeight heights
                    (EvmYul.UInt256.ofNat
                      (block.compactPc + artifact.branchWidth + 1)) ==
                  some (h + 1)) &&
                (lookupHeight heights (EvmYul.UInt256.ofNat dest) ==
                  some (h - 1)) &&
                (lookupHeight heights
                    (EvmYul.UInt256.ofNat
                      (block.compactPc + artifact.branchWidth + 2)) ==
                  some (h - 1))
          | none => false
      | .prim op =>
          if op = .invalid then
            true
          else
            match op.stackArity? with
            | none => true
            | some (input, output) =>
                decide (input ≤ h) &&
                  (lookupHeight heights
                      (EvmYul.UInt256.ofNat (block.compactPc + 1)) ==
                    some (h - input + output))

/-- The trusted validator. -/
def check? (artifact : Compact.Artifact) (cert : Cert) : Bool :=
  heightsBounded? cert.heights &&
    (lookupHeight cert.heights (EvmYul.UInt256.ofNat 0) == some 0) &&
    artifact.blocks.all (blockOk? artifact cert.heights)

/-! ## Untrusted certificate builder -/

/-- Static successor edges of one block for the builder, in `Nat` pc space.
Mirrors the edge relation validated by `blockOk?`. -/
def builderSuccessors (artifact : Compact.Artifact)
    (block : Compact.SourceBlock) (h : Nat) :
    Option (List (Nat × Nat)) :=
  match block.sourceInstr with
  | .label _ => some [(block.compactPc + 1, h)]
  | .push _ =>
      match Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidth block.sourcePc block.sourceInstr with
      | some size => some [(block.compactPc + size, h + 1)]
      | none => none
  | .pushLabel _ => none
  | .jumpDynamic => none
  | .jump target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          some
            [(block.compactPc + artifact.branchWidth + 1, h + 1),
              (dest, h)]
      | none => none
  | .jumpi target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          if 1 ≤ h then
            some
              [(block.compactPc + artifact.branchWidth + 1, h + 1),
                (dest, h - 1),
                (block.compactPc + artifact.branchWidth + 2, h - 1)]
          else none
      | none => none
  | .prim op =>
      if op = .invalid then
        some []
      else
        match op.stackArity? with
        | none => some []
        | some (input, output) =>
            if input ≤ h then
              some [(block.compactPc + 1, h - input + output)]
            else none

def blockTable (blocks : List Compact.SourceBlock) :
    Std.HashMap Nat Compact.SourceBlock :=
  blocks.foldl (fun acc block => acc.insert block.compactPc block)
    Std.HashMap.emptyWithCapacity

def buildLoop (artifact : Compact.Artifact)
    (table : Std.HashMap Nat Compact.SourceBlock) :
    Nat → Std.HashMap Nat Nat → List (Nat × Nat) →
      Option (Std.HashMap Nat Nat)
  | _, acc, [] => some acc
  | 0, _, _ => none
  | fuel + 1, acc, (pc, h) :: work =>
      if h > stackCap then
        none
      else
        match acc.get? pc with
        | some known =>
            if known = h then buildLoop artifact table fuel acc work
            else none
        | none =>
            let acc := acc.insert pc h
            match table.get? pc with
            | none =>
                -- non-block pc (a branch midpoint or the terminal
                -- sentinel): record the height, no further successors here
                -- (midpoint successors are seeded by their own block).
                buildLoop artifact table fuel acc work
            | some block =>
                match builderSuccessors artifact block h with
                | none => none
                | some successors =>
                    buildLoop artifact table fuel acc (successors ++ work)

/-- Untrusted builder: forward single-assignment height propagation from
`pc = 0` at height `0`.  Merge conflicts, unresolved labels, unsupported
instructions, and cap breaches all return `none`. -/
def mkHeights? (artifact : Compact.Artifact) :
    Option (Std.HashMap Nat Nat) :=
  buildLoop artifact (blockTable artifact.blocks)
    (8 * artifact.blocks.length + 8) Std.HashMap.emptyWithCapacity [(0, 0)]

/-- Certificate producer: builds a height table and re-validates it with the
trusted checker.  Returns `none` unless `check?` succeeds. -/
def mkCert? (artifact : Compact.Artifact) : Option Cert := do
  let heights ← mkHeights? artifact
  let cert : Cert :=
    { heights :=
        heights.toList.map (fun entry =>
          (EvmYul.UInt256.ofNat entry.1, entry.2)) }
  if check? artifact cert then some cert else none

theorem mkCert?_check {artifact : Compact.Artifact} {cert : Cert}
    (hMk : mkCert? artifact = some cert) :
    check? artifact cert = true := by
  unfold mkCert? at hMk
  cases hHeights : mkHeights? artifact with
  | none => rw [hHeights] at hMk; simp [bind] at hMk
  | some heights =>
      rw [hHeights] at hMk
      simp only [bind, Option.bind] at hMk
      by_cases hCheck :
          check? artifact
            { heights :=
                heights.toList.map (fun entry =>
                  (EvmYul.UInt256.ofNat entry.1, entry.2)) } = true
      · rw [if_pos hCheck] at hMk
        cases hMk
        exact hCheck
      · rw [if_neg hCheck] at hMk
        cases hMk

/-! ## Validator extraction lemmas -/

theorem lookupHeight_le_cap {heights : HeightList} {pc : Word} {h : Nat}
    (hBounded : heightsBounded? heights = true)
    (hLookup : lookupHeight heights pc = some h) :
    h ≤ stackCap := by
  unfold lookupHeight at hLookup
  cases hFind : heights.find? (fun entry => decide (entry.1 = pc)) with
  | none => rw [hFind] at hLookup; cases hLookup
  | some entry =>
      rw [hFind] at hLookup
      have hMem := List.mem_of_find?_eq_some hFind
      have hAll := List.all_eq_true.mp hBounded entry hMem
      have hEntry : entry.2 = h := by
        simpa using hLookup
      rw [← hEntry]
      simpa using hAll

theorem check?_bounded {artifact : Compact.Artifact} {cert : Cert}
    (hCheck : check? artifact cert = true) :
    heightsBounded? cert.heights = true := by
  unfold check? at hCheck
  simp only [Bool.and_eq_true] at hCheck
  exact hCheck.1.1

theorem check?_anchor {artifact : Compact.Artifact} {cert : Cert}
    (hCheck : check? artifact cert = true) :
    lookupHeight cert.heights (EvmYul.UInt256.ofNat 0) = some 0 := by
  unfold check? at hCheck
  simp only [Bool.and_eq_true, beq_iff_eq] at hCheck
  exact hCheck.1.2

theorem check?_blockOk {artifact : Compact.Artifact} {cert : Cert}
    {block : Compact.SourceBlock}
    (hCheck : check? artifact cert = true)
    (hMem : block ∈ artifact.blocks) :
    blockOk? artifact cert.heights block = true := by
  unfold check? at hCheck
  simp only [Bool.and_eq_true] at hCheck
  exact List.all_eq_true.mp hCheck.2 block hMem

end StackHeadroom
end Assembly
end EvmCompiler
