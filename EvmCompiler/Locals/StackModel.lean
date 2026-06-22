import EvmCompiler.Locals.Syntax
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

def cleanupManyPreserving? : Nat → Nat → Option Structured.Code
  | 0, _temps => some []
  | count + 1, temps => do
      let head ← cleanupOnePreserving? temps
      let tail ← cleanupManyPreserving? count temps
      some (head ++ tail)

def cleanupToPreserving? (ctx : Ctx) (preserve targetDepth : Nat) :
    Option Structured.Code :=
  if targetDepth ≤ ctx.layout.length then
    cleanupManyPreserving? (ctx.layout.length - targetDepth) preserve
  else
    none

@[simp] theorem cleanupManyPreserving?_zero (count : Nat) :
    cleanupManyPreserving? count 0 =
      some
        (List.replicate count
          (Structured.BasicInstr.op .pop)) := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp [cleanupManyPreserving?, cleanupOnePreserving?, ih,
        List.replicate_succ]

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
