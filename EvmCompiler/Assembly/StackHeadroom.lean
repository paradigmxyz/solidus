import EvmCompiler.Assembly.Compact

/-!
# Per-pc abstract-stack-set certificate for compact artifacts

This module defines a decidable operand-stack certificate for compiled
`Compact.Artifact`s together with an executable validator (`check?`).

Design (stage 2, constant-tracking abstract-stack sets):

* the certified abstraction of one operand stack is an `AbsStack`: a list with
  one cell per concrete stack slot, each cell either `some v` (the slot
  provably holds the word `v`) or `none` (unknown);
* the certificate is a table of ADMISSIBLE abstract stacks keyed by physical
  program counter (as an EVM word); a pc may carry several entries, one per
  admissible abstract stack, covering every reachable source-block boundary,
  generated branch midpoint, and the terminal sentinel;
* control flow is read off the compact block layout: every emitted branch is
  a `PUSH dest; JUMP(I)` pair whose destination comes from the compiled label
  table, so all edges are static;
* the table is validated block by block, per admissible abstract stack: every
  abstract stack admitted at a block entry must step (with the block's exact
  abstract effect) to an admitted abstract stack of each static successor,
  and every abstract stack admitted at a branch midpoint must pop to an
  admitted abstract stack of each still-possible branch target — a `JUMPI`
  whose condition cell is a known constant has exactly ONE possible target;
* all admitted abstract stacks are capped at `stackCap` cells, and the anchor
  `[] ∈ stacks(0)` matches a frame entered with an empty stack.

The abstract effects are exact for `PUSH` (a known cell), `DUP`/`SWAP`
(cell-precise permutations) and `EQ` on two known cells (a known boolean
word); every other primitive keeps its declared stack arity and produces
unknown cells.  This is precisely the precision needed by the emitted
function-call return-dispatch protocol: the pushed return token stays a KNOWN
cell while it is buried under the callee frame, so the return dispatcher's
`DUP; PUSH token; EQ; JUMPI` chain folds to a known condition and each
call-site inflow reaches only its own dispatch case.  No merge is performed
across call sites, so no monotone-ratchet false cycle can arise; genuinely
recursive programs grow their abstract stacks past `stackCap` and fail closed
(their concrete stacks really are input-unbounded, so no sound headroom
certificate exists for them).

Soundness against the gasful EVM semantics lives in
`EvmCompiler.Assembly.StackHeadroomSound`.
-/

namespace EvmCompiler
namespace Assembly
namespace StackHeadroom

/-- One abstract operand stack: one cell per concrete slot, known or not. -/
abbrev AbsStack := List (Option Word)

/-- Admissible abstract stacks keyed by physical pc (as an EVM word).  A pc
may occur several times, once per admissible abstract stack. -/
abbrev StackTable := List (Word × AbsStack)

/-- The stack-headroom certificate: a per-pc admissible-abstract-stack table. -/
structure Cert where
  table : StackTable
  deriving Repr, DecidableEq

/-- The certified operand-stack capacity: one below the EVM limit, so that
every instruction (net stack effect at most `+1`) stays within `1024`. -/
def stackCap : Nat := 1023

/-- All abstract stacks admitted at a pc. -/
def stacksAt (table : StackTable) (pc : Word) : List AbsStack :=
  (table.filter (fun entry => decide (entry.1 = pc))).map (·.2)

/-- Whether the abstract stack `astack` is admitted at `pc`. -/
def memStack (table : StackTable) (pc : Word) (astack : AbsStack) : Bool :=
  (stacksAt table pc).any (fun entry => decide (entry = astack))

def stacksBounded? (table : StackTable) : Bool :=
  table.all (fun entry => decide (entry.2.length ≤ stackCap))

/-- Abstract `EQ` on two cells: known exactly when both inputs are known. -/
def absEq : Option Word → Option Word → Option Word
  | some a, some b => some (EvmYul.UInt256.eq a b)
  | _, _ => none

/-- Abstract `DUP n` (callers establish `1 ≤ n ≤ astack.length`). -/
def absDup (n : Nat) (astack : AbsStack) : AbsStack :=
  (astack[n - 1]?.getD none) :: astack

/-- Abstract `SWAP n` (callers establish `n + 1 ≤ astack.length`): exchanges
the top cell with the cell at depth `n`. -/
def absSwap (n : Nat) (astack : AbsStack) : AbsStack :=
  match astack with
  | [] => []
  | top :: rest =>
      (rest[n - 1]?.getD none) ::
        (rest.take (n - 1) ++ top :: rest.drop n)

/-- The exact abstract effect of one nonterminal primitive: cell-precise for
`DUP`/`SWAP`/`EQ`, declared-arity erasure (unknown outputs) otherwise.
`none` when the declared operands do not fit in the abstract stack. -/
def absPrim? (op : PrimOp) (astack : AbsStack) : Option AbsStack :=
  if op = .eq then
    match astack with
    | a :: b :: rest => some (absEq a b :: rest)
    | _ => none
  else
    match op.continuingStep? with
    | some (.dup n) =>
        if 1 ≤ n ∧ n ≤ astack.length then some (absDup n astack) else none
    | some (.swap n) =>
        if 1 ≤ n ∧ n + 1 ≤ astack.length then some (absSwap n astack)
        else none
    | _ =>
        match op.stackArity? with
        | none => none
        | some (input, output) =>
            if input ≤ astack.length then
              some (List.replicate output none ++ astack.drop input)
            else none

/-- Per-block validation of the stack table against the block's static
successors, per admitted abstract stack.  Blocks whose entry admits no
abstract stack are certified unreachable by the surrounding rules and are
skipped (their per-stack checks hold vacuously).  Branch midpoints satisfy a
backward constraint: EVERY abstract stack admitted at the midpoint pops to
admitted abstract stacks of the still-possible branch targets, where a known
`JUMPI` condition cell selects a single target. -/
def blockOk? (artifact : Compact.Artifact) (table : StackTable)
    (block : Compact.SourceBlock) : Bool :=
  match block.sourceInstr with
  | .label _ =>
      (stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).all
        (fun astack =>
          memStack table
            (EvmYul.UInt256.ofNat (block.compactPc + 1)) astack)
  | .push value =>
      match Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidth block.sourcePc block.sourceInstr with
      | some size =>
          (stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).all
            (fun astack =>
              memStack table
                (EvmYul.UInt256.ofNat (block.compactPc + size))
                (some value :: astack))
      | none =>
          (stacksAt table
            (EvmYul.UInt256.ofNat block.compactPc)).isEmpty
  | .pushLabel _ =>
      (stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).isEmpty
  | .jumpDynamic =>
      (stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).isEmpty
  | .jump target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          ((stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).all
            (fun astack =>
              memStack table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))
                (some (EvmYul.UInt256.ofNat dest) :: astack))) &&
            ((stacksAt table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).all
              (fun mid =>
                match mid with
                | _ :: rest =>
                    memStack table (EvmYul.UInt256.ofNat dest) rest
                | [] => false))
      | none =>
          (stacksAt table
              (EvmYul.UInt256.ofNat block.compactPc)).isEmpty &&
            (stacksAt table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).isEmpty
  | .jumpi target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          ((stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).all
            (fun astack =>
              memStack table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))
                (some (EvmYul.UInt256.ofNat dest) :: astack))) &&
            ((stacksAt table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).all
              (fun mid =>
                match mid with
                | _ :: cond :: rest =>
                    (match cond with
                      | some c =>
                          if c = EvmYul.UInt256.ofNat 0 then
                            memStack table
                              (EvmYul.UInt256.ofNat
                                (block.compactPc + artifact.branchWidth + 2))
                              rest
                          else
                            memStack table (EvmYul.UInt256.ofNat dest) rest
                      | none =>
                          memStack table (EvmYul.UInt256.ofNat dest) rest &&
                            memStack table
                              (EvmYul.UInt256.ofNat
                                (block.compactPc + artifact.branchWidth + 2))
                              rest)
                | _ => false))
      | none =>
          (stacksAt table
              (EvmYul.UInt256.ofNat block.compactPc)).isEmpty &&
            (stacksAt table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).isEmpty
  | .prim op =>
      if op = .invalid then
        true
      else
        match op.stackArity? with
        | none => true
        | some _ =>
            (stacksAt table (EvmYul.UInt256.ofNat block.compactPc)).all
              (fun astack =>
                match absPrim? op astack with
                | some astack' =>
                    memStack table
                      (EvmYul.UInt256.ofNat (block.compactPc + 1)) astack'
                | none => false)

/-- The trusted validator. -/
def check? (artifact : Compact.Artifact) (cert : Cert) : Bool :=
  stacksBounded? cert.table &&
    memStack cert.table (EvmYul.UInt256.ofNat 0) [] &&
    artifact.blocks.all (blockOk? artifact cert.table)

/-! ## Indexed validator

`check?` answers every `stacksAt`/`memStack` query with a linear scan of the
whole flat table, so validating a table of `E` entries against `B` blocks
costs on the order of `B * E` table-element visits — prohibitive on large
production runtimes (tens of billions of visits).  `checkIndexed?` groups
the table once into per-pc buckets keyed by `Word.toNat` and answers every
query from the relevant bucket.  It is proved EQUAL to `check?`
(`checkIndexed?_eq_check?`), in both directions at once, so `mkCert?` may
call it while every soundness lemma stays keyed on `check?`. -/

/-- Per-pc bucket index of a flat stack table, keyed by `Word.toNat`.
Bucket order is the reverse of table order; only membership matters. -/
def indexTable (table : StackTable) : Std.HashMap Nat (List AbsStack) :=
  table.foldl
    (fun acc entry =>
      acc.insert entry.1.toNat (entry.2 :: acc.getD entry.1.toNat []))
    Std.HashMap.emptyWithCapacity

/-- Indexed counterpart of `stacksAt`. -/
def stacksAtIdx (idx : Std.HashMap Nat (List AbsStack)) (pc : Word) :
    List AbsStack :=
  idx.getD pc.toNat []

/-- Indexed counterpart of `memStack`. -/
def memStackIdx (idx : Std.HashMap Nat (List AbsStack)) (pc : Word)
    (astack : AbsStack) : Bool :=
  (stacksAtIdx idx pc).any (fun entry => decide (entry = astack))

theorem word_toNat_inj {a b : Word} (h : EvmYul.UInt256.toNat a =
    EvmYul.UInt256.toNat b) : a = b := by
  cases a; cases b
  simp only [EvmYul.UInt256.toNat] at h
  congr 1
  exact Fin.ext h

/-- Membership in the buckets built by the `indexTable` fold. -/
theorem indexTable_fold_mem (l : StackTable)
    (acc : Std.HashMap Nat (List AbsStack)) (k : Nat) (a : AbsStack) :
    a ∈ (l.foldl
        (fun acc entry =>
          acc.insert entry.1.toNat (entry.2 :: acc.getD entry.1.toNat []))
        acc).getD k [] ↔
      a ∈ acc.getD k [] ∨
        ∃ p, p ∈ l ∧ EvmYul.UInt256.toNat p.1 = k ∧ p.2 = a := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
      rw [List.foldl_cons, ih]
      have hIns :
          a ∈ (acc.insert hd.1.toNat
              (hd.2 :: acc.getD hd.1.toNat [])).getD k [] ↔
            a ∈ acc.getD k [] ∨
              (EvmYul.UInt256.toNat hd.1 = k ∧ hd.2 = a) := by
        rw [Std.HashMap.getD_insert]
        by_cases hk : EvmYul.UInt256.toNat hd.1 = k
        · subst hk
          simp [List.mem_cons, eq_comm, or_comm]
        · simp [hk, Ne.symm hk]
      rw [hIns]
      constructor
      · rintro ((hAcc | ⟨hPc, hStack⟩) | ⟨p, hMem, hPc, hStack⟩)
        · exact Or.inl hAcc
        · exact Or.inr ⟨hd, List.mem_cons_self .., hPc, hStack⟩
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hMem, hPc, hStack⟩
      · rintro (hAcc | ⟨p, hMem, hPc, hStack⟩)
        · exact Or.inl (Or.inl hAcc)
        · rcases List.mem_cons.mp hMem with hHd | hTl
          · subst hHd
            exact Or.inl (Or.inr ⟨hPc, hStack⟩)
          · exact Or.inr ⟨p, hTl, hPc, hStack⟩

theorem mem_stacksAt_iff {table : StackTable} {pc : Word} {a : AbsStack} :
    a ∈ stacksAt table pc ↔ ∃ p, p ∈ table ∧ p.1 = pc ∧ p.2 = a := by
  unfold stacksAt
  constructor
  · intro hMem
    obtain ⟨p, hFilter, hEq⟩ := List.mem_map.mp hMem
    obtain ⟨hTable, hPc⟩ := List.mem_filter.mp hFilter
    exact ⟨p, hTable, of_decide_eq_true hPc, hEq⟩
  · rintro ⟨p, hTable, hPc, hStack⟩
    exact List.mem_map.mpr
      ⟨p, List.mem_filter.mpr ⟨hTable, decide_eq_true hPc⟩, hStack⟩

/-- The bucket index answers exactly the flat-table membership queries. -/
theorem mem_stacksAtIdx_iff {table : StackTable} {pc : Word}
    {a : AbsStack} :
    a ∈ stacksAtIdx (indexTable table) pc ↔ a ∈ stacksAt table pc := by
  unfold stacksAtIdx indexTable
  rw [indexTable_fold_mem, mem_stacksAt_iff]
  constructor
  · rintro (hEmpty | ⟨p, hMem, hPc, hStack⟩)
    · simp at hEmpty
    · exact ⟨p, hMem, word_toNat_inj hPc, hStack⟩
  · rintro ⟨p, hMem, hPc, hStack⟩
    exact Or.inr ⟨p, hMem, by rw [hPc], hStack⟩

theorem memStackIdx_eq (table : StackTable) (pc : Word)
    (astack : AbsStack) :
    memStackIdx (indexTable table) pc astack = memStack table pc astack := by
  rw [Bool.eq_iff_iff]
  unfold memStackIdx memStack
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨entry, hMem, hEq⟩
    exact ⟨entry, mem_stacksAtIdx_iff.mp hMem, hEq⟩
  · rintro ⟨entry, hMem, hEq⟩
    exact ⟨entry, mem_stacksAtIdx_iff.mpr hMem, hEq⟩

theorem stacksAtIdx_all_eq (table : StackTable) (pc : Word)
    (f : AbsStack → Bool) :
    (stacksAtIdx (indexTable table) pc).all f = (stacksAt table pc).all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hAll a hMem
    exact hAll a (mem_stacksAtIdx_iff.mpr hMem)
  · intro hAll a hMem
    exact hAll a (mem_stacksAtIdx_iff.mp hMem)

theorem stacksAtIdx_isEmpty_eq (table : StackTable) (pc : Word) :
    (stacksAtIdx (indexTable table) pc).isEmpty =
      (stacksAt table pc).isEmpty := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff,
    List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro hNone a hMem
    exact hNone a (mem_stacksAtIdx_iff.mpr hMem)
  · intro hNone a hMem
    exact hNone a (mem_stacksAtIdx_iff.mp hMem)

/-- Indexed mirror of `blockOk?`: same per-block, per-abstract-stack rules,
every table query answered from the per-pc bucket index. -/
def blockOkIdx? (artifact : Compact.Artifact)
    (idx : Std.HashMap Nat (List AbsStack))
    (block : Compact.SourceBlock) : Bool :=
  match block.sourceInstr with
  | .label _ =>
      (stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).all
        (fun astack =>
          memStackIdx idx
            (EvmYul.UInt256.ofNat (block.compactPc + 1)) astack)
  | .push value =>
      match Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidth block.sourcePc block.sourceInstr with
      | some size =>
          (stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).all
            (fun astack =>
              memStackIdx idx
                (EvmYul.UInt256.ofNat (block.compactPc + size))
                (some value :: astack))
      | none =>
          (stacksAtIdx idx
            (EvmYul.UInt256.ofNat block.compactPc)).isEmpty
  | .pushLabel _ =>
      (stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).isEmpty
  | .jumpDynamic =>
      (stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).isEmpty
  | .jump target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          ((stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).all
            (fun astack =>
              memStackIdx idx
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))
                (some (EvmYul.UInt256.ofNat dest) :: astack))) &&
            ((stacksAtIdx idx
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).all
              (fun mid =>
                match mid with
                | _ :: rest =>
                    memStackIdx idx (EvmYul.UInt256.ofNat dest) rest
                | [] => false))
      | none =>
          (stacksAtIdx idx
              (EvmYul.UInt256.ofNat block.compactPc)).isEmpty &&
            (stacksAtIdx idx
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).isEmpty
  | .jumpi target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          ((stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).all
            (fun astack =>
              memStackIdx idx
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))
                (some (EvmYul.UInt256.ofNat dest) :: astack))) &&
            ((stacksAtIdx idx
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).all
              (fun mid =>
                match mid with
                | _ :: cond :: rest =>
                    (match cond with
                      | some c =>
                          if c = EvmYul.UInt256.ofNat 0 then
                            memStackIdx idx
                              (EvmYul.UInt256.ofNat
                                (block.compactPc + artifact.branchWidth + 2))
                              rest
                          else
                            memStackIdx idx (EvmYul.UInt256.ofNat dest) rest
                      | none =>
                          memStackIdx idx (EvmYul.UInt256.ofNat dest) rest &&
                            memStackIdx idx
                              (EvmYul.UInt256.ofNat
                                (block.compactPc + artifact.branchWidth + 2))
                              rest)
                | _ => false))
      | none =>
          (stacksAtIdx idx
              (EvmYul.UInt256.ofNat block.compactPc)).isEmpty &&
            (stacksAtIdx idx
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 1))).isEmpty
  | .prim op =>
      if op = .invalid then
        true
      else
        match op.stackArity? with
        | none => true
        | some _ =>
            (stacksAtIdx idx (EvmYul.UInt256.ofNat block.compactPc)).all
              (fun astack =>
                match absPrim? op astack with
                | some astack' =>
                    memStackIdx idx
                      (EvmYul.UInt256.ofNat (block.compactPc + 1)) astack'
                | none => false)

theorem blockOkIdx?_eq (artifact : Compact.Artifact) (table : StackTable)
    (block : Compact.SourceBlock) :
    blockOkIdx? artifact (indexTable table) block =
      blockOk? artifact table block := by
  unfold blockOkIdx? blockOk?
  cases block.sourceInstr <;>
    simp only [memStackIdx_eq, stacksAtIdx_all_eq, stacksAtIdx_isEmpty_eq]

/-- The fast validator: identical verdict to `check?`
(`checkIndexed?_eq_check?`), bucket-indexed table queries. -/
def checkIndexed? (artifact : Compact.Artifact) (cert : Cert) : Bool :=
  let idx := indexTable cert.table
  stacksBounded? cert.table &&
    memStackIdx idx (EvmYul.UInt256.ofNat 0) [] &&
    artifact.blocks.all (blockOkIdx? artifact idx)

/-- Full behavioural equality of the fast and flat validators: no
certificate changes verdict in either direction. -/
theorem checkIndexed?_eq_check? (artifact : Compact.Artifact)
    (cert : Cert) :
    checkIndexed? artifact cert = check? artifact cert := by
  simp only [checkIndexed?, check?]
  have hBlocks :
      blockOkIdx? artifact (indexTable cert.table) =
        blockOk? artifact cert.table :=
    funext (blockOkIdx?_eq artifact cert.table)
  rw [memStackIdx_eq, hBlocks]

/-! ## Untrusted certificate builder -/

/-- Static successor edges of one block for the builder, in `Nat` pc space.
Mirrors the per-abstract-stack edge relation validated by `blockOk?`. -/
def builderSuccessors (artifact : Compact.Artifact)
    (block : Compact.SourceBlock) (astack : AbsStack) :
    Option (List (Nat × AbsStack)) :=
  match block.sourceInstr with
  | .label _ => some [(block.compactPc + 1, astack)]
  | .push value =>
      match Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidth block.sourcePc block.sourceInstr with
      | some size => some [(block.compactPc + size, some value :: astack)]
      | none => none
  | .pushLabel _ => none
  | .jumpDynamic => none
  | .jump target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          some
            [(block.compactPc + artifact.branchWidth + 1,
              some (EvmYul.UInt256.ofNat dest) :: astack),
              (dest, astack)]
      | none => none
  | .jumpi target =>
      match Compact.lookupLabel? artifact.labels target with
      | some dest =>
          match astack with
          | cond :: rest =>
              let mid :=
                (block.compactPc + artifact.branchWidth + 1,
                  some (EvmYul.UInt256.ofNat dest) :: cond :: rest)
              match cond with
              | some c =>
                  if c = EvmYul.UInt256.ofNat 0 then
                    some
                      [mid,
                        (block.compactPc + artifact.branchWidth + 2, rest)]
                  else some [mid, (dest, rest)]
              | none =>
                  some
                    [mid, (dest, rest),
                      (block.compactPc + artifact.branchWidth + 2, rest)]
          | [] => none
      | none => none
  | .prim op =>
      if op = .invalid then
        some []
      else
        match op.stackArity? with
        | none => some []
        | some _ =>
            match absPrim? op astack with
            | some astack' => some [(block.compactPc + 1, astack')]
            | none => none

def blockTable (blocks : List Compact.SourceBlock) :
    Std.HashMap Nat Compact.SourceBlock :=
  blocks.foldl (fun acc block => acc.insert block.compactPc block)
    Std.HashMap.emptyWithCapacity

def buildLoop (artifact : Compact.Artifact)
    (table : Std.HashMap Nat Compact.SourceBlock) :
    Nat → Std.HashMap Nat (List AbsStack) → List (Nat × AbsStack) →
      Option (Std.HashMap Nat (List AbsStack))
  | _, acc, [] => some acc
  | 0, _, _ => none
  | fuel + 1, acc, (pc, astack) :: work =>
      if astack.length > stackCap then
        none
      else
        let known := (acc.get? pc).getD []
        if known.contains astack then
          buildLoop artifact table fuel acc work
        else
          let acc := acc.insert pc (astack :: known)
          match table.get? pc with
          | none =>
              -- non-block pc (a branch midpoint or the terminal
              -- sentinel): record the abstract stack, no further
              -- successors here (midpoint successors are seeded by their
              -- own block).
              buildLoop artifact table fuel acc work
          | some block =>
              match builderSuccessors artifact block astack with
              | none => none
              | some successors =>
                  buildLoop artifact table fuel acc (successors ++ work)

/-- Untrusted builder: forward abstract-stack-set propagation from `pc = 0`
with the empty stack.  Visited `⟨pc, abstract stack⟩` pairs are accumulated
as per-pc sets, so shared procedure bodies entered under several call frames
get one entry per inflow; unresolved labels, unsupported instructions, and
cap breaches all return `none`.  The fuel bounds the worklist; runs whose
abstract state space stays modest (every non-recursive emitted program)
finish long before exhausting it, and pathological programs fail closed. -/
def mkStacks? (artifact : Compact.Artifact) :
    Option (Std.HashMap Nat (List AbsStack)) :=
  buildLoop artifact (blockTable artifact.blocks)
    (16 * (stackCap + 1) * (artifact.blocks.length + 1) + 16)
    Std.HashMap.emptyWithCapacity [(0, [])]

/-- Certificate producer: builds an abstract-stack-set table and re-validates
it with the fast validator `checkIndexed?` (proved equal to the trusted
`check?` by `checkIndexed?_eq_check?`, so the accepted set is unchanged).
Returns `none` unless the validation succeeds. -/
def mkCert? (artifact : Compact.Artifact) : Option Cert := do
  let built ← mkStacks? artifact
  let cert : Cert :=
    { table :=
        built.toList.flatMap (fun entry =>
          entry.2.map (fun astack =>
            (EvmYul.UInt256.ofNat entry.1, astack))) }
  if checkIndexed? artifact cert then some cert else none

theorem mkCert?_check {artifact : Compact.Artifact} {cert : Cert}
    (hMk : mkCert? artifact = some cert) :
    check? artifact cert = true := by
  unfold mkCert? at hMk
  cases hStacks : mkStacks? artifact with
  | none => rw [hStacks] at hMk; simp [bind] at hMk
  | some built =>
      rw [hStacks] at hMk
      simp only [bind, Option.bind] at hMk
      by_cases hCheck :
          checkIndexed? artifact
            { table :=
                built.toList.flatMap (fun entry =>
                  entry.2.map (fun astack =>
                    (EvmYul.UInt256.ofNat entry.1, astack))) } = true
      · rw [if_pos hCheck] at hMk
        cases hMk
        rw [← checkIndexed?_eq_check?]
        exact hCheck
      · rw [if_neg hCheck] at hMk
        cases hMk

/-! ## Validator extraction lemmas -/

theorem memStack_eq_true_iff {table : StackTable} {pc : Word}
    {astack : AbsStack} :
    memStack table pc astack = true ↔ astack ∈ stacksAt table pc := by
  unfold memStack
  rw [List.any_eq_true]
  constructor
  · rintro ⟨entry, hMem, hEq⟩
    have hEntry : entry = astack := of_decide_eq_true hEq
    subst hEntry
    exact hMem
  · intro hMem
    exact ⟨astack, hMem, by simp⟩

/-- Apply a per-stack `all` fact of the validator at one admitted abstract
stack. -/
theorem all_stacksAt_apply {table : StackTable} {pc : Word}
    {f : AbsStack → Bool} {astack : AbsStack}
    (hAll : (stacksAt table pc).all f = true)
    (hMem : memStack table pc astack = true) : f astack = true :=
  List.all_eq_true.mp hAll astack (memStack_eq_true_iff.mp hMem)

theorem memStack_length_le_cap {table : StackTable} {pc : Word}
    {astack : AbsStack}
    (hBounded : stacksBounded? table = true)
    (hMem : memStack table pc astack = true) :
    astack.length ≤ stackCap := by
  have hIn := memStack_eq_true_iff.mp hMem
  unfold stacksAt at hIn
  obtain ⟨entry, hEntryMem, hEntryEq⟩ := List.mem_map.mp hIn
  have hMemList := (List.mem_filter.mp hEntryMem).1
  have hAll := List.all_eq_true.mp hBounded entry hMemList
  rw [← hEntryEq]
  simpa using hAll

theorem check?_bounded {artifact : Compact.Artifact} {cert : Cert}
    (hCheck : check? artifact cert = true) :
    stacksBounded? cert.table = true := by
  unfold check? at hCheck
  simp only [Bool.and_eq_true] at hCheck
  exact hCheck.1.1

theorem check?_anchor {artifact : Compact.Artifact} {cert : Cert}
    (hCheck : check? artifact cert = true) :
    memStack cert.table (EvmYul.UInt256.ofNat 0) [] = true := by
  unfold check? at hCheck
  simp only [Bool.and_eq_true] at hCheck
  exact hCheck.1.2

theorem check?_blockOk {artifact : Compact.Artifact} {cert : Cert}
    {block : Compact.SourceBlock}
    (hCheck : check? artifact cert = true)
    (hMem : block ∈ artifact.blocks) :
    blockOk? artifact cert.table block = true := by
  unfold check? at hCheck
  simp only [Bool.and_eq_true] at hCheck
  exact List.all_eq_true.mp hCheck.2 block hMem

end StackHeadroom
end Assembly
end EvmCompiler
