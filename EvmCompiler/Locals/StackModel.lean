import EvmCompiler.Locals.Syntax

namespace EvmCompiler
namespace Locals

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

def promoteNameStackOnly? (ctx : Ctx) (name : Name) :
    Option (Structured.Code × Layout) := do
  let depth ← Layout.lookupDepth? name ctx.layout
  let idx := depth - 1
  if idx ≤ 16 then
    let code ← swapRestoreUpTo? idx
    some (code, Layout.promoteAt idx ctx.layout)
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

def cleanupAll (ctx : Ctx) : Structured.Code :=
  List.replicate ctx.layout.length (Structured.BasicInstr.op .pop)

end Ctx

end Locals
end EvmCompiler
