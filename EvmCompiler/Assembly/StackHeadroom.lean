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
it with the trusted checker.  Returns `none` unless `check?` succeeds. -/
def mkCert? (artifact : Compact.Artifact) : Option Cert := do
  let built ← mkStacks? artifact
  let cert : Cert :=
    { table :=
        built.toList.flatMap (fun entry =>
          entry.2.map (fun astack =>
            (EvmYul.UInt256.ofNat entry.1, astack))) }
  if check? artifact cert then some cert else none

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
          check? artifact
            { table :=
                built.toList.flatMap (fun entry =>
                  entry.2.map (fun astack =>
                    (EvmYul.UInt256.ofNat entry.1, astack))) } = true
      · rw [if_pos hCheck] at hMk
        cases hMk
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
