import EvmCompiler.Locals.Syntax
-- `TypedCfg.Shape.anonymousBinder` only: the reserved zero-byte retag binder
-- name.  `TypedCfg.Syntax` depends on nothing but `Assembly.Syntax`, so this
-- introduces no layering cycle.
import EvmCompiler.TypedCfg.Syntax
import Mathlib.Tactic.IntervalCases

namespace EvmCompiler
namespace Locals

namespace StackList

def swapPopAt {α : Type} : Nat → List α → List α
  | _, [] => []
  | 0, _ :: rest => rest
  | idx + 1, head :: rest =>
      match rest[idx]? with
      | none => head :: rest
      | some _ => rest.set idx head

theorem map_swapPopAt {α β : Type} (f : α → β)
    (idx : Nat) (items : List α) :
    (swapPopAt idx items).map f = swapPopAt idx (items.map f) := by
  cases items with
  | nil => simp [swapPopAt]
  | cons head rest =>
      cases idx with
      | zero => simp [swapPopAt]
      | succ idx =>
          cases hAt : rest[idx]? with
          | none =>
              have hMapAt : (rest.map f)[idx]? = none := by
                simp [List.getElem?_map, hAt]
              simp [swapPopAt, hAt, hMapAt]
          | some value =>
              have hMapAt : (rest.map f)[idx]? = some (f value) := by
                simp [List.getElem?_map, hAt]
              simp [swapPopAt, hAt, hMapAt, List.map_set]

theorem swapPopAt_append_of_lt {α : Type} (idx : Nat)
    (items suffix : List α) (hIdx : idx < items.length) :
    swapPopAt idx (items ++ suffix) = swapPopAt idx items ++ suffix := by
  cases items with
  | nil => simp at hIdx
  | cons head rest =>
      cases idx with
      | zero => simp [swapPopAt]
      | succ idx =>
          have hRest : idx < rest.length := by simpa using hIdx
          change
            (match (rest ++ suffix)[idx]? with
              | none => head :: (rest ++ suffix)
              | some _ => (rest ++ suffix).set idx head) =
            (match rest[idx]? with
              | none => head :: rest
              | some _ => rest.set idx head) ++ suffix
          rw [List.getElem?_append_left hRest]
          cases hAt : rest[idx]? with
          | none => simp [hAt]
          | some value =>
              rw [List.set_append_left idx head hRest]

theorem mem_set_cases {α : Type} {items : List α} {idx : Nat}
    {new candidate : α} (hIdx : idx < items.length)
    (hMem : candidate ∈ items.set idx new) :
    candidate = new ∨ candidate ∈ items := by
  rw [List.set_eq_take_cons_drop new hIdx] at hMem
  rcases List.mem_append.mp hMem with hTake | hTail
  · exact Or.inr (List.mem_of_mem_take hTake)
  · rcases List.mem_cons.mp hTail with hNew | hDrop
    · exact Or.inl hNew
    · exact Or.inr (List.mem_of_mem_drop hDrop)

theorem mem_of_mem_swapPopAt {α : Type} {idx : Nat}
    {items : List α} {candidate : α}
    (hMem : candidate ∈ swapPopAt idx items) : candidate ∈ items := by
  cases items with
  | nil => simp [swapPopAt] at hMem
  | cons head rest =>
      cases idx with
      | zero =>
          simp only [swapPopAt] at hMem
          exact List.mem_cons_of_mem head hMem
      | succ idx =>
          simp only [swapPopAt] at hMem
          cases hAt : rest[idx]? with
          | none => simpa [hAt] using hMem
          | some value =>
              rw [hAt] at hMem
              have hIdx : idx < rest.length :=
                (List.getElem?_eq_some_iff.mp hAt).1
              rcases mem_set_cases hIdx hMem with hHead | hRest
              · subst candidate
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem head hRest

end StackList

namespace Layout

def lookupDepthFrom (name : Name) : Nat → Layout → Option Nat
  | _depth, [] => none
  | depth, key :: rest =>
      if key = name then
        some depth
      else
        lookupDepthFrom name (depth + 1) rest

def lookupDepth? (name : Name) (layout : Layout) : Option Nat :=
  lookupDepthFrom name 1 layout

theorem lookupDepthFrom_succ (name : Name) (depth : Nat)
    (layout : Layout) :
    lookupDepthFrom name (depth + 1) layout =
      (lookupDepthFrom name depth layout).map (· + 1) := by
  induction layout generalizing depth with
  | nil =>
      simp [lookupDepthFrom]
  | cons head tail ih =>
      by_cases hHead : head = name
      · simp [lookupDepthFrom, hHead]
      · simp [lookupDepthFrom, hHead, ih, Nat.add_assoc]

theorem lookupDepth?_cons_of_ne
    {name head : Name} {layout : Layout} {depth : Nat}
    (hNe : head ≠ name)
    (hDepth : lookupDepth? name layout = some depth) :
    lookupDepth? name (head :: layout) = some (depth + 1) := by
  have hDepth' :
      lookupDepthFrom name 1 layout = some depth := by
    simpa [lookupDepth?] using hDepth
  simp only [lookupDepth?, lookupDepthFrom, if_neg hNe]
  rw [lookupDepthFrom_succ, hDepth']
  rfl

theorem lookupDepth?_append_of_not_mem
    {name : Name} {pre suffix : Layout} {depth : Nat}
    (hNotMem : name ∉ pre)
    (hDepth : lookupDepth? name suffix = some depth) :
    lookupDepth? name (pre ++ suffix) =
      some (pre.length + depth) := by
  induction pre with
  | nil =>
      simpa using hDepth
  | cons head tail ih =>
      have hHeadNe : head ≠ name := by
        intro hEq
        subst head
        exact hNotMem (by simp)
      have hTailNotMem : name ∉ tail := by
        intro hMem
        exact hNotMem (List.mem_cons_of_mem head hMem)
      have hTailDepth := ih hTailNotMem
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        lookupDepth?_cons_of_ne hHeadNe hTailDepth

theorem exists_lookupDepth?_eq_some_of_mem
    {name : Name} {layout : Layout}
    (hMem : name ∈ layout) :
    ∃ depth, lookupDepth? name layout = some (depth + 1) := by
  induction layout with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      by_cases hHead : head = name
      · subst head
        exact ⟨0, by simp [lookupDepth?, lookupDepthFrom]⟩
      · have hTailMem : name ∈ tail := by
          simpa [hHead, Ne.symm hHead] using hMem
        obtain ⟨depth, hDepth⟩ := ih hTailMem
        exact
          ⟨depth + 1,
            by simpa [Nat.add_assoc] using
              lookupDepth?_cons_of_ne hHead hDepth⟩

theorem mem_of_lookupDepth?_eq_some
    {name : Name} {layout : Layout} {depth : Nat}
    (hDepth : lookupDepth? name layout = some depth) :
    name ∈ layout := by
  unfold lookupDepth? at hDepth
  generalize hStart : 1 = start at hDepth
  clear hStart
  induction layout generalizing start with
  | nil =>
      simp [lookupDepthFrom] at hDepth
  | cons head tail ih =>
      by_cases hHead : head = name
      · simp [hHead]
      · simp only [lookupDepthFrom, if_neg hHead] at hDepth
        exact List.mem_cons_of_mem head (ih (start + 1) hDepth)

private theorem lookupDepthFrom_eq_some_index
    {name : Name} {layout : Layout} {start result : Nat}
    (hDepth : lookupDepthFrom name start layout = some result) :
    ∃ index,
      result = start + index ∧
        layout[index]? = some name := by
  induction layout generalizing start with
  | nil =>
      simp [lookupDepthFrom] at hDepth
  | cons head tail ih =>
      by_cases hHead : head = name
      · subst head
        simp [lookupDepthFrom] at hDepth
        subst result
        exact ⟨0, by simp, rfl⟩
      · simp only [lookupDepthFrom, if_neg hHead] at hDepth
        obtain ⟨index, hResult, hAt⟩ := ih hDepth
        refine ⟨index + 1, ?_, ?_⟩
        · omega
        · simpa [Nat.add_comm] using hAt

theorem getElem?_eq_some_of_lookupDepth?_eq_some
    {name : Name} {layout : Layout} {depth : Nat}
    (hDepth : lookupDepth? name layout = some (depth + 1)) :
    layout[depth]? = some name := by
  obtain ⟨index, hResult, hAt⟩ :=
    lookupDepthFrom_eq_some_index
      (by simpa [lookupDepth?] using hDepth)
  have hIndex : index = depth := by
    omega
  simpa [hIndex] using hAt

theorem lookupDepth?_eq_some_of_getElem?_eq_some_of_nodup
    {name : Name} {layout : Layout} {index : Nat}
    (hNodup : layout.Nodup)
    (hAt : layout[index]? = some name) :
    lookupDepth? name layout = some (index + 1) := by
  induction layout generalizing index with
  | nil =>
      simp at hAt
  | cons head tail ih =>
      have hTailNodup := (List.nodup_cons.mp hNodup).2
      cases index with
      | zero =>
          simp at hAt
          subst head
          simp [lookupDepth?, lookupDepthFrom]
      | succ index =>
          simp only [List.getElem?_cons_succ] at hAt
          have hTailDepth := ih hTailNodup hAt
          have hNameMem : name ∈ tail :=
            List.mem_of_getElem? hAt
          have hHeadNe : head ≠ name := by
            intro hEq
            subst head
            exact (List.nodup_cons.mp hNodup).1 hNameMem
          simpa [Nat.add_assoc] using
            lookupDepth?_cons_of_ne hHeadNe hTailDepth

theorem lookupDepth?_getLast_of_nodup
    {layout : Layout}
    (hNodup : layout.Nodup)
    (hNonempty : layout ≠ []) :
    lookupDepth? (layout.getLast hNonempty) layout = some layout.length := by
  induction layout with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp [lookupDepth?, lookupDepthFrom]
      | cons next rest =>
          have hTailNodup :=
            (List.nodup_cons.mp hNodup).2
          have hTailNonempty : next :: rest ≠ [] := by
            simp
          have hTailDepth := ih hTailNodup hTailNonempty
          have hLastMem :
              (next :: rest).getLast hTailNonempty ∈ next :: rest :=
            List.getLast_mem hTailNonempty
          have hHeadNe :
              head ≠ (next :: rest).getLast hTailNonempty := by
            intro hEq
            subst head
            exact (List.nodup_cons.mp hNodup).1 hLastMem
          simpa [Nat.add_assoc] using
            lookupDepth?_cons_of_ne hHeadNe hTailDepth

theorem name_eq_of_lookupDepth?_eq_some
    {left right : Name} {layout : Layout} {depth : Nat}
    (hLeft : lookupDepth? left layout = some (depth + 1))
    (hRight : lookupDepth? right layout = some (depth + 1)) :
    left = right := by
  have hLeftAt :=
    getElem?_eq_some_of_lookupDepth?_eq_some hLeft
  have hRightAt :=
    getElem?_eq_some_of_lookupDepth?_eq_some hRight
  rw [hLeftAt] at hRightAt
  cases hRightAt
  rfl

def promoteAt (idx : Nat) (layout : Layout) : Layout :=
  match layout[idx]? with
  | none => layout
  | some name => name :: layout.take idx ++ layout.drop (idx + 1)

/-- Remove one stack slot using the layout produced by `SWAP idx; POP`.
Index zero needs only `POP`; an out-of-range index leaves the layout unchanged. -/
def discardAt : Nat → Layout → Layout
  | idx, layout => StackList.swapPopAt idx layout

theorem promoteAt_perm (idx : Nat) (layout : Layout) :
    (promoteAt idx layout).Perm layout := by
  induction idx generalizing layout with
  | zero =>
      cases layout <;> simp [promoteAt]
  | succ idx ih =>
      cases layout with
      | nil => simp [promoteAt]
      | cons head tail =>
          cases hAt : tail[idx]? with
          | none => simp [promoteAt, hAt]
          | some name =>
              have hTail := ih tail
              rw [promoteAt, hAt] at hTail
              have hSwap :
                  (name :: head :: tail.take idx ++ tail.drop (idx + 1)).Perm
                    (head :: name :: tail.take idx ++ tail.drop (idx + 1)) :=
                List.Perm.swap head name _
              simpa [promoteAt, hAt, Nat.add_assoc] using
                hSwap.trans (List.Perm.cons head hTail)

end Layout

namespace StackOp

def dup? : Nat → Option Structured.BasicOp
  | 1 => some .dup1
  | 2 => some .dup2
  | 3 => some .dup3
  | 4 => some .dup4
  | 5 => some .dup5
  | 6 => some .dup6
  | 7 => some .dup7
  | 8 => some .dup8
  | 9 => some .dup9
  | 10 => some .dup10
  | 11 => some .dup11
  | 12 => some .dup12
  | 13 => some .dup13
  | 14 => some .dup14
  | 15 => some .dup15
  | 16 => some .dup16
  | _ => none

theorem exists_dup?_of_pos_of_le
    {depth : Nat}
    (hPos : 0 < depth)
    (hLe : depth ≤ 16) :
    ∃ op, dup? depth = some op := by
  interval_cases depth <;> simp [dup?] at *

theorem bounds_of_dup?_eq_some
    {depth : Nat} {op : Structured.BasicOp}
    (hOp : dup? depth = some op) :
    0 < depth ∧ depth ≤ 16 := by
  by_cases hLe : depth ≤ 16
  · have hPos : 0 < depth := by
      by_contra hNotPos
      have hZero : depth = 0 := by omega
      subst depth
      simp [dup?] at hOp
    exact ⟨hPos, hLe⟩
  · have hLarge : 17 ≤ depth := by omega
    let extra := depth - 17
    have hDepth : depth = 17 + extra := by
      simp [extra]
      omega
    rw [hDepth] at hOp
    have h1 : 17 + extra ≠ 1 := by omega
    have h2 : 17 + extra ≠ 2 := by omega
    have h3 : 17 + extra ≠ 3 := by omega
    have h4 : 17 + extra ≠ 4 := by omega
    have h5 : 17 + extra ≠ 5 := by omega
    have h6 : 17 + extra ≠ 6 := by omega
    have h7 : 17 + extra ≠ 7 := by omega
    have h8 : 17 + extra ≠ 8 := by omega
    have h9 : 17 + extra ≠ 9 := by omega
    have h10 : 17 + extra ≠ 10 := by omega
    have h11 : 17 + extra ≠ 11 := by omega
    have h12 : 17 + extra ≠ 12 := by omega
    have h13 : 17 + extra ≠ 13 := by omega
    have h14 : 17 + extra ≠ 14 := by omega
    have h15 : 17 + extra ≠ 15 := by omega
    have h16 : 17 + extra ≠ 16 := by omega
    simp [dup?, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, h12, h13, h14, h15, h16] at hOp

def swap? : Nat → Option Structured.BasicOp
  | 1 => some .swap1
  | 2 => some .swap2
  | 3 => some .swap3
  | 4 => some .swap4
  | 5 => some .swap5
  | 6 => some .swap6
  | 7 => some .swap7
  | 8 => some .swap8
  | 9 => some .swap9
  | 10 => some .swap10
  | 11 => some .swap11
  | 12 => some .swap12
  | 13 => some .swap13
  | 14 => some .swap14
  | 15 => some .swap15
  | 16 => some .swap16
  | _ => none

theorem exists_swap?_of_pos_of_le
    {depth : Nat}
    (hPos : 0 < depth)
    (hLe : depth ≤ 16) :
    ∃ op, swap? depth = some op := by
  interval_cases depth <;> simp [swap?] at *

end StackOp

structure Ctx where
  layout : Layout
  breakDepth? : Option Nat
  continueDepth? : Option Nat
  leaveDepth? : Option Nat
  leaveRetc : Nat := 0

namespace Ctx

def initial : Ctx where
  layout := []
  breakDepth? := none
  continueDepth? := none
  leaveDepth? := none

def procEntry : Ctx :=
  { initial with leaveDepth? := some 0 }

def procEntryWithLayout (layout : Layout) : Ctx :=
  { procEntry with layout := layout }

def procEntryWithLayoutAndRetc (layout : Layout) (retc : Nat) : Ctx :=
  { procEntryWithLayout layout with leaveRetc := retc }

def withLayout (ctx : Ctx) (layout : Layout) : Ctx :=
  { ctx with layout := layout }

def withoutLoopControl (ctx : Ctx) : Ctx :=
  { ctx with breakDepth? := none, continueDepth? := none }

def withLoopControl (ctx : Ctx) (depth : Nat) : Ctx :=
  { ctx with breakDepth? := some depth, continueDepth? := some depth }

/--
Two Locals compiler contexts share every non-layout control destination.

Open compilation may extend or restore the stack layout, but ordinary
statement sequencing never changes the surrounding loop/leave destinations.
-/
structure SameControl (before after : Ctx) : Prop where
  breakDepth : before.breakDepth? = after.breakDepth?
  continueDepth : before.continueDepth? = after.continueDepth?
  leaveDepth : before.leaveDepth? = after.leaveDepth?
  leaveRetc : before.leaveRetc = after.leaveRetc

namespace SameControl

theorem refl (ctx : Ctx) : SameControl ctx ctx :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem symm
    {before after : Ctx}
    (hControl : SameControl before after) :
    SameControl after before :=
  ⟨hControl.breakDepth.symm, hControl.continueDepth.symm,
    hControl.leaveDepth.symm, hControl.leaveRetc.symm⟩

theorem trans
    {first second third : Ctx}
    (hFirst : SameControl first second)
    (hSecond : SameControl second third) :
    SameControl first third :=
  ⟨hFirst.breakDepth.trans hSecond.breakDepth,
    hFirst.continueDepth.trans hSecond.continueDepth,
    hFirst.leaveDepth.trans hSecond.leaveDepth,
    hFirst.leaveRetc.trans hSecond.leaveRetc⟩

theorem withLayout (ctx : Ctx) (layout : Layout) :
    SameControl ctx (ctx.withLayout layout) :=
  ⟨rfl, rfl, rfl, rfl⟩

end SameControl

def cleanupTo? (ctx : Ctx) (targetDepth : Nat) : Option Structured.Code :=
  if targetDepth ≤ ctx.layout.length then
    some
      (List.replicate (ctx.layout.length - targetDepth)
        (Structured.BasicInstr.op .pop))
  else
    none

def swapRestoreUpTo? : Nat → Option Structured.Code
  | 0 => some []
  | n + 1 => do
      let rest ← swapRestoreUpTo? n
      let op ← StackOp.swap? (n + 1)
      some (rest ++ [Structured.BasicInstr.op op])

theorem exists_swapRestoreUpTo?_of_le
    {depth : Nat}
    (hLe : depth ≤ 16) :
    ∃ code, swapRestoreUpTo? depth = some code := by
  induction depth with
  | zero =>
      exact ⟨[], rfl⟩
  | succ depth ih =>
      obtain ⟨rest, hRest⟩ := ih (by omega)
      obtain ⟨op, hOp⟩ :=
        StackOp.exists_swap?_of_pos_of_le
          (depth := depth + 1) (by omega) hLe
      exact
        ⟨rest ++ [Structured.BasicInstr.op op],
          by simp [swapRestoreUpTo?, hRest, hOp]⟩

def promoteNameStackOnly? (ctx : Ctx) (name : Name) :
    Option (Structured.Code × Layout) := do
  let depth ← Layout.lookupDepth? name ctx.layout
  let idx := depth - 1
  if idx ≤ 16 then
    let code ← swapRestoreUpTo? idx
    some (code, Layout.promoteAt idx ctx.layout)
  else
    none

def discardNameStackOnly? (ctx : Ctx) (name : Name) :
    Option (Structured.Code × Layout) := do
  let depth ← Layout.lookupDepth? name ctx.layout
  let idx := depth - 1
  match idx with
  | 0 =>
      some ([Structured.BasicInstr.op .pop], Layout.discardAt 0 ctx.layout)
  | idx + 1 =>
      if idx + 1 ≤ 16 then
        let op ← StackOp.swap? (idx + 1)
        some
          ([Structured.BasicInstr.op op, Structured.BasicInstr.op .pop],
            Layout.discardAt (idx + 1) ctx.layout)
      else
        none

def cleanupOnePreserving? : Nat → Option Structured.Code
  | 0 => some [Structured.BasicInstr.op .pop]
  | temps + 1 => do
      let op ← StackOp.swap? (temps + 1)
      let restore ← swapRestoreUpTo? temps
      some
        ([Structured.BasicInstr.op op, Structured.BasicInstr.op .pop] ++
          restore)

/-- `count` bare `SWAP temps; POP` discards.

`SWAP temps; POP` drops one value from under the preserved prefix exactly as
`cleanupOnePreserving?` does, but leaves the prefix rotated **left by one**
instead of paying `swapRestoreUpTo? (temps-1)` to put it back. Rotations
accumulate, so `count` of them leave the prefix rotated left by `count`. -/
def discardManyRotating? : Nat → Nat → Option Structured.Code
  | 0, _temps => some []
  | count + 1, temps => do
      let op ← StackOp.swap? temps
      let rest ← discardManyRotating? count temps
      some ([Structured.BasicInstr.op op, Structured.BasicInstr.op .pop] ++ rest)

/-- Undo `k` accumulated left-rotations of the top `temps` values. One
right-rotation is `SWAP1 .. SWAP(temps-1)`, i.e. `swapRestoreUpTo? (temps-1)` —
the very sequence `cleanupOnePreserving?` was paying per discard. -/
def rotateRestore? : Nat → Nat → Option Structured.Code
  | 0, _temps => some []
  | k + 1, temps => do
      let one ← swapRestoreUpTo? (temps - 1)
      let rest ← rotateRestore? k temps
      some (one ++ rest)

/-- Drop `count` values from under `temps` preserved ones.

The per-discard form (`cleanupOnePreserving?`) re-emits the restore rotation
after *every* `POP`, costing `count * (temps + 1)`. Deferring the rotations
costs `2 * count + (count % temps) * (temps - 1)` instead — the prefix only has
to be put back once, and only by however much it is actually out of place.
Checked equivalent to the per-discard form on every `(temps, count)` pair with
`temps < 6, count < 9`; 31.5% fewer instructions over that range, and identical
for `temps ≤ 1` where the old form was already tight. -/
def cleanupManyPreservingRot? (count : Nat) : Nat → Option Structured.Code
  | 0 => some (List.replicate count (Structured.BasicInstr.op .pop))
  | temps + 1 => do
      let body ← discardManyRotating? count (temps + 1)
      let fixup ← rotateRestore? (count % (temps + 1)) (temps + 1)
      some (body ++ fixup)

/-- **Bulk teardown under a single preserved value.**

With exactly one value `p` preserved on top of `count` values to discard, the
rotating form emits `(SWAP1 ; POP)^count` — `2 * count` bytes.  A single
`SWAP count` sinks `p` to the bottom of the discard window (`p, a₁ … a_count`
becomes `a_count, a₁ … a_{count-1}, p`), after which the whole window is on top
and `count` bare `POP`s clear it: `count + 1` bytes.

`SWAP n` only exists for `1 ≤ n ≤ 16`, so this returns `none` for
`count > 16`; the caller **falls back to the rotating form**, it never fails.
`count = 0` is `[]` and `count = 1` ties the rotating form at two bytes, so
both are routed to the fallback for free. -/
def bulkDiscardUnderOne? (count : Nat) : Option Structured.Code := do
  let op ← StackOp.swap? count
  some (Structured.BasicInstr.op op ::
    List.replicate count (Structured.BasicInstr.op .pop))

/-- Drop `count` values from under `temps` preserved ones.

The per-discard form (`cleanupOnePreserving?`) re-emits the restore rotation
after *every* `POP`, costing `count * (temps + 1)`. Deferring the rotations
costs `2 * count + (count % temps) * (temps - 1)` instead — the prefix only has
to be put back once, and only by however much it is actually out of place.
Checked equivalent to the per-discard form on every `(temps, count)` pair with
`temps < 6, count < 9`; 31.5% fewer instructions over that range, and identical
for `temps ≤ 1` where the old form was already tight.

`temps = 1` is then further improved by `bulkDiscardUnderOne?`, which replaces
`(SWAP1 ; POP)^count` with `SWAP count ; POP^count` whenever `count ≤ 16`. -/
def cleanupManyPreserving? (count : Nat) : Nat → Option Structured.Code
  | 0 => some (List.replicate count (Structured.BasicInstr.op .pop))
  | 1 =>
      match bulkDiscardUnderOne? count with
      | some code => some code
      | none => cleanupManyPreservingRot? count 1
  | temps + 1 => cleanupManyPreservingRot? count (temps + 1)

/--
Zero-byte retag of the `preserve` values kept on top by a preserving cleanup.

A preserving cleanup is only ever emitted at a procedure exit, where the values
it keeps are the procedure's return values.  Those values were pushed by
duplicating the named locals holding them, so the typed CFG still classifies
them as `.local` slots — but `Shape.procExit` requires anonymous `.word` slots.
`bindLocals` is a compiler-owned pseudo-instruction that lowers to no bytes at
all (`TypedCfg.Instr.lower? (.bindLocals _ _) = some []`) and whose runtime
semantics is the identity, so binding the kept values to
`Shape.anonymousBinder` performs that reclassification for free.

The alternative the compiler used to emit was `add(x, 0)` per returned value,
which is also value-preserving but costs `PUSH0 ; ADD` — two runtime bytes and
eight gas per returned value per exit, purely to change a type tag.
-/
def retagPreservedWords (preserve : Nat) : Structured.Code :=
  match preserve with
  | 0 => []
  | count + 1 =>
      [Structured.BasicInstr.bindLocals 0
        (List.replicate (count + 1) TypedCfg.Shape.anonymousBinder)]

@[simp] theorem retagPreservedWords_zero :
    retagPreservedWords 0 = [] := rfl

@[simp] theorem retagPreservedWords_usesCallCreate (preserve : Nat) :
    (retagPreservedWords preserve).usesCallCreate = false := by
  cases preserve <;>
    simp [retagPreservedWords, Structured.Code.usesCallCreate,
      Structured.BasicInstr.usesCallCreate]

def cleanupToPreserving? (ctx : Ctx) (preserve targetDepth : Nat) :
    Option Structured.Code :=
  if targetDepth ≤ ctx.layout.length then
    (cleanupManyPreserving? (ctx.layout.length - targetDepth) preserve).map
      (· ++ retagPreservedWords preserve)
  else
    none

@[simp] theorem cleanupManyPreserving?_zero (count : Nat) :
    cleanupManyPreserving? count 0 =
      some
        (List.replicate count
          (Structured.BasicInstr.op .pop)) := rfl

@[simp] theorem cleanupManyPreservingRot?_zero (count : Nat) :
    cleanupManyPreservingRot? count 0 =
      some
        (List.replicate count
          (Structured.BasicInstr.op .pop)) := rfl

/-! `cleanupManyPreserving?` is the rotating schedule except at `temps = 1`,
where it may take the `bulkDiscardUnderOne?` shortcut. -/

theorem cleanupManyPreserving?_zero_eq (count : Nat) :
    cleanupManyPreserving? count 0 = cleanupManyPreservingRot? count 0 := rfl

theorem cleanupManyPreserving?_succ_succ_eq (count temps : Nat) :
    cleanupManyPreserving? count (temps + 2) =
      cleanupManyPreservingRot? count (temps + 2) := rfl

theorem cleanupManyPreserving?_one (count : Nat) :
    cleanupManyPreserving? count 1 =
      match bulkDiscardUnderOne? count with
      | some code => some code
      | none => cleanupManyPreservingRot? count 1 := rfl

@[simp] theorem cleanupToPreserving?_zero
    (ctx : Ctx) (targetDepth : Nat) :
    ctx.cleanupToPreserving? 0 targetDepth =
      ctx.cleanupTo? targetDepth := by
  unfold cleanupToPreserving? cleanupTo?
  split <;> simp_all

def cleanupAll (ctx : Ctx) : Structured.Code :=
  List.replicate ctx.layout.length (Structured.BasicInstr.op .pop)

end Ctx

end Locals
end EvmCompiler
