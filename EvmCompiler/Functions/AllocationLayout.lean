import EvmCompiler.Functions.AllocationLiveness
import EvmCompiler.Locals.StackModel

/-!
Checked symbolic-stack transitions owned by Functions allocation.

This module does not choose liveness or emit lower code.  It turns a current
layout and a demanded live set into a checked sequence of top-16 promotions
followed by one suffix cleanup.  The relative order of retained names is the
current canonical order, which makes the operation suitable at control joins.
-/

namespace EvmCompiler
namespace Functions
namespace AllocationLayout

open AllocationLiveness

structure Promotion where
  name : Name
  depth : Nat
  deriving DecidableEq, Repr

structure Schedule where
  promotions : List Promotion
  promoted : Locals.Layout
  target : Locals.Layout
  deriving DecidableEq, Repr

def Promotion.apply? (layout : Locals.Layout)
    (promotion : Promotion) : Option Locals.Layout := do
  let sourceDepth ← Locals.Layout.lookupDepth? promotion.name layout
  if sourceDepth = promotion.depth ∧ sourceDepth ≤ 17 then
    some (Locals.Layout.promoteAt (promotion.depth - 1) layout)
  else
    none

def run : Locals.Layout → List Promotion → Option Locals.Layout
  | layout, [] => some layout
  | layout, promotion :: rest => do
      let promoted ← promotion.apply? layout
      run promoted rest

def build : Locals.Layout → List Name → Option (List Promotion × Locals.Layout)
  | layout, [] => some ([], layout)
  | layout, name :: rest => do
      let sourceDepth ← Locals.Layout.lookupDepth? name layout
      if sourceDepth ≤ 17 then
        let promoted := Locals.Layout.promoteAt (sourceDepth - 1) layout
        let (tail, final) ← build promoted rest
        some ({ name, depth := sourceDepth } :: tail, final)
      else
        none

theorem build_run
    {layout : Locals.Layout} {names : List Name}
    {promotions : List Promotion} {final : Locals.Layout}
    (hBuild : build layout names = some (promotions, final)) :
    run layout promotions = some final := by
  induction names generalizing layout promotions final with
  | nil =>
      simp [build] at hBuild
      rcases hBuild with ⟨rfl, rfl⟩
      rfl
  | cons name rest ih =>
      unfold build at hBuild
      cases hDepth : Locals.Layout.lookupDepth? name layout with
      | none => simp [hDepth] at hBuild
      | some depth =>
          by_cases hAccessible : depth ≤ 17
          · simp [hDepth, hAccessible] at hBuild
            cases hTail :
                build (Locals.Layout.promoteAt (depth - 1) layout) rest with
            | none => simp [hTail] at hBuild
            | some result =>
                rcases result with ⟨tail, tailFinal⟩
                rw [hTail] at hBuild
                have hPair := Option.some.inj hBuild
                injection hPair with hPromotions hFinal
                subst promotions
                subst final
                have hApply :
                    Promotion.apply? layout { name := name, depth := depth } =
                      some (Locals.Layout.promoteAt (depth - 1) layout) := by
                  simp [Promotion.apply?, hDepth, hAccessible]
                rw [run, hApply]
                exact ih hTail
          · simp [hDepth, hAccessible] at hBuild

def retained (layout : Locals.Layout) (live : LiveSet) : Locals.Layout :=
  layout.filter fun name => decide (name ∈ live)

def dead (layout : Locals.Layout) (live : LiveSet) : List Name :=
  layout.filter fun name => decide (name ∉ live)

def scheduleRetain? (layout : Locals.Layout)
    (live : LiveSet) : Option Schedule := do
  let (promotions, promoted) ← build layout (dead layout live)
  let target := retained layout live
  if target = promoted.drop (promoted.length - target.length) then
    some { promotions, promoted, target }
  else
    none

def Schedule.ValidFor (schedule : Schedule)
    (layout : Locals.Layout) (live : LiveSet) : Prop :=
  run layout schedule.promotions = some schedule.promoted ∧
    schedule.target = retained layout live ∧
    schedule.target =
      schedule.promoted.drop
        (schedule.promoted.length - schedule.target.length)

theorem scheduleRetain?_sound
    {layout : Locals.Layout} {live : LiveSet} {schedule : Schedule}
    (hSchedule : scheduleRetain? layout live = some schedule) :
    schedule.ValidFor layout live := by
  unfold scheduleRetain? at hSchedule
  cases hBuild : build layout (dead layout live) with
  | none => simp [hBuild] at hSchedule
  | some result =>
      rcases result with ⟨promotions, promoted⟩
      rw [hBuild] at hSchedule
      change
        (if retained layout live =
              promoted.drop
                (promoted.length - (retained layout live).length) then
            some
              { promotions := promotions
                promoted := promoted
                target := retained layout live }
          else
            none) = some schedule at hSchedule
      by_cases hSuffix :
          retained layout live =
            promoted.drop (promoted.length - (retained layout live).length)
      · rw [if_pos hSuffix] at hSchedule
        have hEq := Option.some.inj hSchedule
        subst schedule
        exact ⟨build_run hBuild, rfl, hSuffix⟩
      · rw [if_neg hSuffix] at hSchedule
        contradiction

def Schedule.statements (schedule : Schedule) : List Locals.Stmt :=
  (schedule.promotions.map fun promotion =>
      Locals.Stmt.promoteName promotion.name) ++
    [Locals.Stmt.cleanupTo schedule.target]

namespace Examples

def retainAlternating? : Option Schedule :=
  scheduleRetain? ["a", "b", "c", "d"] {"b", "d"}

theorem retainAlternating_target :
    retainAlternating?.map Schedule.target = some ["b", "d"] := by
  decide

theorem retainAlternating_promoted :
    retainAlternating?.map Schedule.promoted =
      some ["c", "a", "b", "d"] := by
  decide

def inaccessibleBottom? : Option Schedule :=
  let layout := (List.range 18).map fun index => "v" ++ toString index
  scheduleRetain? layout
    (layout.take 17).toFinset

theorem inaccessibleBottom_rejected : inaccessibleBottom? = none := by
  decide

end Examples

end AllocationLayout
end Functions
end EvmCompiler
