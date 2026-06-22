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

theorem Promotion.apply?_perm
    {layout promoted : Locals.Layout} {promotion : Promotion}
    (hApply : promotion.apply? layout = some promoted) :
    promoted.Perm layout := by
  unfold Promotion.apply? at hApply
  cases hDepth : Locals.Layout.lookupDepth? promotion.name layout with
  | none => simp [hDepth] at hApply
  | some depth =>
      by_cases hAllowed :
          depth = promotion.depth ∧ depth ≤ 17
      · simp [hDepth, hAllowed] at hApply
        rw [← hApply.2]
        exact Locals.Layout.promoteAt_perm _ _
      · simp [hDepth, hAllowed] at hApply

theorem run_perm
    {layout finalLayout : Locals.Layout} {promotions : List Promotion}
    (hRun : run layout promotions = some finalLayout) :
    finalLayout.Perm layout := by
  induction promotions generalizing layout with
  | nil =>
      simp [run] at hRun
      subst finalLayout
      exact List.Perm.refl _
  | cons promotion rest ih =>
      unfold run at hRun
      cases hApply : promotion.apply? layout with
      | none => simp [hApply] at hRun
      | some promoted =>
          rw [hApply] at hRun
          exact (ih hRun).trans (promotion.apply?_perm hApply)

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

structure Discard where
  name : Name
  depth : Nat
  deriving DecidableEq, Repr

def Discard.apply? (layout : Locals.Layout)
    (discard : Discard) : Option Locals.Layout := do
  let sourceDepth ← Locals.Layout.lookupDepth? discard.name layout
  if sourceDepth = discard.depth ∧ sourceDepth ≤ 17 then
    some (Locals.Layout.discardAt (discard.depth - 1) layout)
  else
    none

def runDiscards : Locals.Layout → List Discard → Option Locals.Layout
  | layout, [] => some layout
  | layout, discard :: rest => do
      let discarded ← discard.apply? layout
      runDiscards discarded rest

def buildDiscards : Locals.Layout → List Name →
    Option (List Discard × Locals.Layout)
  | layout, [] => some ([], layout)
  | layout, name :: rest => do
      let sourceDepth ← Locals.Layout.lookupDepth? name layout
      if sourceDepth ≤ 17 then
        let discarded := Locals.Layout.discardAt (sourceDepth - 1) layout
        let (tail, final) ← buildDiscards discarded rest
        some ({ name, depth := sourceDepth } :: tail, final)
      else
        none

theorem buildDiscards_run
    {layout : Locals.Layout} {names : List Name}
    {discards : List Discard} {final : Locals.Layout}
    (hBuild : buildDiscards layout names = some (discards, final)) :
    runDiscards layout discards = some final := by
  induction names generalizing layout discards final with
  | nil =>
      simp [buildDiscards] at hBuild
      rcases hBuild with ⟨rfl, rfl⟩
      rfl
  | cons name rest ih =>
      unfold buildDiscards at hBuild
      cases hDepth : Locals.Layout.lookupDepth? name layout with
      | none => simp [hDepth] at hBuild
      | some depth =>
          by_cases hAccessible : depth ≤ 17
          · simp [hDepth, hAccessible] at hBuild
            cases hTail :
                buildDiscards
                  (Locals.Layout.discardAt (depth - 1) layout) rest with
            | none => simp [hTail] at hBuild
            | some result =>
                rcases result with ⟨tail, tailFinal⟩
                rw [hTail] at hBuild
                have hPair := Option.some.inj hBuild
                injection hPair with hDiscards hFinal
                subst discards
                subst final
                have hApply :
                    Discard.apply? layout { name := name, depth := depth } =
                      some (Locals.Layout.discardAt (depth - 1) layout) := by
                  simp [Discard.apply?, hDepth, hAccessible]
                rw [runDiscards, hApply]
                exact ih hTail
          · simp [hDepth, hAccessible] at hBuild

structure DiscardSchedule where
  source : Locals.Layout
  live : LiveSet
  discards : List Discard
  target : Locals.Layout
  valid : runDiscards source discards = some target
  targetSet : target.toFinset = source.toFinset ∩ live
  targetNodup : target.Nodup

def DiscardSchedule.statements (schedule : DiscardSchedule) :
    List Locals.Stmt :=
  schedule.discards.map fun discard => .discardName discard.name

def scheduleDiscards? (layout : Locals.Layout)
    (live : LiveSet) : Option DiscardSchedule :=
  match hBuild : buildDiscards layout (dead layout live) with
  | none => none
  | some (discards, target) =>
      if hSet : target.toFinset = layout.toFinset ∩ live then
        if hNodup : target.Nodup then
          some
            { source := layout
              live
              discards
              target
              valid := buildDiscards_run hBuild
              targetSet := hSet
              targetNodup := hNodup }
        else
          none
      else
        none

theorem scheduleDiscards?_sound
    {layout : Locals.Layout} {live : LiveSet}
    {schedule : DiscardSchedule}
    (hSchedule : scheduleDiscards? layout live = some schedule) :
    schedule.source = layout ∧
      schedule.live = live ∧
      runDiscards layout schedule.discards = some schedule.target ∧
      schedule.target.toFinset = layout.toFinset ∩ live ∧
      schedule.target.Nodup := by
  unfold scheduleDiscards? at hSchedule
  split at hSchedule
  · contradiction
  · rename_i discards target hBuild
    split at hSchedule
    · rename_i hSet
      split at hSchedule
      · rename_i hNodup
        simp only [Option.some.injEq] at hSchedule
        subst schedule
        exact ⟨rfl, rfl, buildDiscards_run hBuild, hSet, hNodup⟩
      · contradiction
    · contradiction

/-- A straight-line liveness transition. Unlike the canonical `Transition`
used at joins, this may permute surviving names while directly removing dead
slots. -/
structure RegularTransition where
  schedule : DiscardSchedule

namespace RegularTransition

def build? (layout : Locals.Layout) (live : LiveSet) :
    Option RegularTransition := do
  let schedule ← scheduleDiscards? layout live
  some { schedule }

def source (transition : RegularTransition) : Locals.Layout :=
  transition.schedule.source

def live (transition : RegularTransition) : LiveSet :=
  transition.schedule.live

def target (transition : RegularTransition) : Locals.Layout :=
  transition.schedule.target

def statements (transition : RegularTransition) : List Locals.Stmt :=
  transition.schedule.statements ++ [.cleanupTo transition.target]

def cost (transition : RegularTransition) : Nat :=
  transition.schedule.discards.length

theorem build?_sound
    {layout : Locals.Layout} {live : LiveSet}
    {transition : RegularTransition}
    (hBuild : build? layout live = some transition) :
    transition.source = layout ∧ transition.live = live ∧
      runDiscards layout transition.schedule.discards =
        some transition.target := by
  unfold build? at hBuild
  cases hSchedule : scheduleDiscards? layout live with
  | none => simp [hSchedule] at hBuild
  | some schedule =>
      simp [hSchedule] at hBuild
      subst transition
      exact
        ⟨(scheduleDiscards?_sound hSchedule).1,
          (scheduleDiscards?_sound hSchedule).2.1,
          (scheduleDiscards?_sound hSchedule).2.2.1⟩

theorem target_nodup (transition : RegularTransition) :
    transition.target.Nodup :=
  transition.schedule.targetNodup

end RegularTransition

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

/-- A retain transition together with the proof computed by its owner. -/
structure Transition where
  source : Locals.Layout
  live : LiveSet
  schedule : Schedule
  valid : schedule.ValidFor source live

namespace Transition

def build? (layout : Locals.Layout) (live : LiveSet) : Option Transition :=
  match hSchedule : scheduleRetain? layout live with
  | none => none
  | some schedule =>
      some
        { source := layout
          live
          schedule
          valid := scheduleRetain?_sound hSchedule }

def target (transition : Transition) : Locals.Layout :=
  transition.schedule.target

theorem build?_sound
    {layout : Locals.Layout} {live : LiveSet} {transition : Transition}
    (hBuild : build? layout live = some transition) :
    transition.source = layout ∧
      transition.live = live ∧
      transition.schedule.ValidFor layout live := by
  unfold build? at hBuild
  split at hBuild
  · simp_all
  · rename_i schedule hSchedule
    simp only [Option.some.injEq] at hBuild
    subst transition
    exact ⟨rfl, rfl, scheduleRetain?_sound hSchedule⟩

theorem target_nodup
    (transition : Transition)
    (hSource : transition.source.Nodup) :
    transition.schedule.target.Nodup := by
  rw [transition.valid.2.1]
  exact hSource.filter _

end Transition

/-- A pure stack permutation used to place imminent accesses near the top.
Unlike `Transition`, it drops no values. -/
structure Ordering where
  source : Locals.Layout
  promotions : List Promotion
  target : Locals.Layout
  valid : run source promotions = some target

namespace Ordering

def build? (layout : Locals.Layout) (topFirst : List Name) : Option Ordering :=
  match hBuild : build layout topFirst.reverse with
  | none => none
  | some (promotions, target) =>
      some
        { source := layout
          promotions
          target
          valid := build_run hBuild }

theorem build?_source
    {layout : Locals.Layout} {topFirst : List Name} {ordering : Ordering}
    (hBuild : build? layout topFirst = some ordering) :
    ordering.source = layout := by
  unfold build? at hBuild
  split at hBuild
  · contradiction
  · cases hBuild
    rfl

theorem target_perm (ordering : Ordering) :
    ordering.target.Perm ordering.source :=
  run_perm ordering.valid

theorem target_nodup (ordering : Ordering)
    (hSource : ordering.source.Nodup) :
    ordering.target.Nodup :=
  ordering.target_perm.nodup_iff.mpr hSource

theorem target_mem_iff (ordering : Ordering) {name : Name} :
    name ∈ ordering.target ↔ name ∈ ordering.source :=
  ordering.target_perm.mem_iff

def statements (ordering : Ordering) : List Locals.Stmt :=
  ordering.promotions.map fun promotion =>
    Locals.Stmt.promoteName promotion.name

end Ordering

def commonPrefixLength : Locals.Layout → Locals.Layout → Nat
  | left :: leftRest, right :: rightRest =>
      if left = right then
        1 + commonPrefixLength leftRest rightRest
      else
        0
  | _, _ => 0

def commonSuffixLength (left right : Locals.Layout) : Nat :=
  commonPrefixLength left.reverse right.reverse

/-- Checked restoration of a canonical control-flow layout. Child-local values
are removed first; only the differing top prefix is then reordered, leaving an
already-equal dormant suffix untouched. -/
structure Join where
  source : Locals.Layout
  target : Locals.Layout
  retain : Transition
  order : Ordering
  retainSource : retain.source = source
  orderSource : order.source = retain.target
  orderTarget : order.target = target

namespace Join

def build? (source target : Locals.Layout) : Option Join := do
  match hRetain : Transition.build? source target.toFinset with
  | none => none
  | some retain =>
      let common := commonSuffixLength retain.target target
      let desiredPrefix := target.take (target.length - common)
      match hOrder : build retain.target desiredPrefix.reverse with
      | none => none
      | some (promotions, ordered) =>
          if hTarget : ordered = target then
            some
              { source
                target
                retain
                order :=
                  { source := retain.target
                    promotions
                    target := ordered
                    valid := build_run hOrder }
                retainSource := (Transition.build?_sound hRetain).1
                orderSource := rfl
                orderTarget := hTarget }
          else
            none

theorem build?_endpoints
    {source target : Locals.Layout} {join : Join}
    (hBuild : build? source target = some join) :
    join.source = source ∧ join.target = target := by
  unfold build? at hBuild
  split at hBuild
  · contradiction
  · rename_i retain hRetain
    dsimp only at hBuild
    split at hBuild
    · contradiction
    · all_goals
        split at hBuild
        · simp only [Option.some.injEq] at hBuild
          subst join
          exact ⟨rfl, rfl⟩
        · contradiction

theorem target_nodup (join : Join) (hSource : join.source.Nodup) :
    join.target.Nodup := by
  rw [← join.orderTarget]
  apply join.order.target_nodup
  rw [join.orderSource]
  apply join.retain.target_nodup
  rwa [join.retainSource]

def statements (join : Join) : List Locals.Stmt :=
  (join.retain.schedule.promotions.map fun promotion =>
      Locals.Stmt.promoteName promotion.name) ++
    [Locals.Stmt.cleanupTo join.retain.schedule.target] ++
    join.order.statements

end Join

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
