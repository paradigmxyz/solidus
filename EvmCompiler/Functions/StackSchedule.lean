import EvmCompiler.Functions.AllocationLivenessFacts
import EvmCompiler.Functions.AllocationLayout

/-!
Forward symbolic stack scheduling over compiler-owned liveness facts.

This pass chooses no scratch locations and emits no code.  It checks that every
source demand is present, preserves enclosing layouts across structured
regions, establishes one loop baseline, and computes an adjacent
`AllocationLayout.Schedule` at every fallthrough boundary.
-/

namespace EvmCompiler
namespace Functions
namespace StackSchedule

open AllocationLiveness
open AllocationLivenessFacts
open AllocationLayout

mutual
  structure Region where
    entry : Transition
    points : List Point
    finalLayout : Locals.Layout

  structure Point where
    beforeLayout : Locals.Layout
    statementLayout : Locals.Layout
    retain? : Option Transition
    regions : List Region := []
    fallsThrough : Bool := true
end

def layoutSet (layout : Locals.Layout) : LiveSet :=
  layout.toFinset

def required (pinned live : LiveSet) : LiveSet :=
  pinned ∪ live

/-- Mutable definitions do not read their old value, but stack lowering still
needs the destination slot resident until the write has executed. -/
def residentBefore (stmt : Stmt)
    (facts : AllocationLivenessFacts.Point) : LiveSet :=
  facts.liveBefore ∪
    match stmt with
    | .assign name _ => {name}
    | .call targets _ _ => targets.toFinset
    | _ => ∅

def blockEntryLive (source : Block)
    (facts : AllocationLivenessFacts.Region) : LiveSet :=
  match source.stmts, facts.points with
  | stmt :: _, point :: _ => residentBefore stmt point
  | _, _ => facts.liveIn

def nextLive (fallback : LiveSet) :
    List Stmt → List AllocationLivenessFacts.Point → LiveSet
  | stmt :: _, point :: _ => residentBefore stmt point
  | _, _ => fallback

def covers (layout : Locals.Layout) (live : LiveSet) : Prop :=
  live ⊆ layoutSet layout

instance coversDecidable (layout : Locals.Layout) (live : LiveSet) :
    Decidable (covers layout live) := by
  unfold covers layoutSet
  infer_instance

def alwaysExits : Stmt → Bool
  | .brk | .cont | .leave | .terminal _ | .terminalArgs _ _ => true
  | _ => false

mutual
  def scheduleBlockFuel
      (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout)
      (source : Block) (facts : AllocationLivenessFacts.Region) :
      Option Region :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
        let entryDemand := required pinned (blockEntryLive source facts)
        if covers layout entryDemand then
        let entry ← Transition.build? layout entryDemand
        let (points, finalLayout) ←
          scheduleStmtListFuel fuel pinned entry.target
            source.stmts facts.points
        some { entry, points, finalLayout }
        else
          none

  def scheduleStmtListFuel
      (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout) :
      List Stmt → List AllocationLivenessFacts.Point →
        Option (List Point × Locals.Layout)
    | [], [] => some ([], layout)
    | stmt :: rest, facts :: restFacts => do
        if covers layout (residentBefore stmt facts) then
        let point ← scheduleStmtFuel fuel pinned layout stmt facts
        if point.fallsThrough then
          let afterDemand :=
            required pinned (nextLive facts.liveAfter rest restFacts)
          if covers point.statementLayout afterDemand then
          let retain ← Transition.build? point.statementLayout afterDemand
          let point := { point with retain? := some retain }
          let (tail, finalLayout) ←
            scheduleStmtListFuel fuel pinned retain.target rest restFacts
          some (point :: tail, finalLayout)
          else
            none
        else
          some ({ point with retain? := none } :: [], point.statementLayout)
        else
          none
    | _, _ => none

  def scheduleCaseRegionsFuel
      (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout) :
      List (Word × Block) → List AllocationLivenessFacts.Region →
        Option (List Region)
    | [], [] => some []
    | (_, body) :: rest, facts :: restFacts => do
        let head ← scheduleBlockFuel fuel pinned layout body facts
        let tail ←
          scheduleCaseRegionsFuel fuel pinned layout rest restFacts
        some (head :: tail)
    | _, _ => none

  def scheduleDefaultRegionFuel
      (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout) :
      Option Block → List AllocationLivenessFacts.Region →
        Option (List Region)
    | none, [] => some []
    | some body, [facts] => do
        let region ← scheduleBlockFuel fuel pinned layout body facts
        some [region]
    | _, _ => none

  def scheduleStmtFuel
      (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout)
      (stmt : Stmt) (facts : AllocationLivenessFacts.Point) : Option Point :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match stmt with
        | .let_ name _ =>
            if name ∈ layout then
              none
            else
              some
                { beforeLayout := layout
                  statementLayout := name :: layout
                  retain? := none }
        | .block body =>
            match facts.regions with
            | [bodyFacts] => do
                let region ←
                  scheduleBlockFuel fuel (layoutSet layout) layout
                    body bodyFacts
                some
                  { beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    regions := [region] }
            | _ => none
        | .if_ _ body =>
            match facts.regions with
            | [bodyFacts] => do
                let region ←
                  scheduleBlockFuel fuel (layoutSet layout) layout
                    body bodyFacts
                some
                  { beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    regions := [region] }
            | _ => none
        | .switch _ cases defaultBody => do
            let caseCount := cases.length
            let caseFacts := facts.regions.take caseCount
            let defaultFacts := facts.regions.drop caseCount
            let branchProtected := layoutSet layout
            let caseRegions ←
              scheduleCaseRegionsFuel fuel branchProtected layout
                cases caseFacts
            let defaultRegions ←
              scheduleDefaultRegionFuel fuel branchProtected layout
                defaultBody defaultFacts
            some
              { beforeLayout := layout
                statementLayout := layout
                retain? := none
                regions := caseRegions ++ defaultRegions }
        | .for_ init _ post body =>
            match facts.regions, facts.loop? with
            | [initFacts, postFacts, bodyFacts], some _loop => do
                let outerProtected := layoutSet layout
                let initRegion ←
                  scheduleBlockFuel fuel outerProtected layout init initFacts
                let baseline := initRegion.finalLayout
                let loopProtected := layoutSet baseline
                let postRegion ←
                  scheduleBlockFuel fuel loopProtected baseline post postFacts
                let bodyRegion ←
                  scheduleBlockFuel fuel loopProtected baseline body bodyFacts
                some
                  { beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    regions := [initRegion, postRegion, bodyRegion] }
            | _, _ => none
        | _ =>
            some
              { beforeLayout := layout
                statementLayout := layout
                retain? := none
                fallsThrough := !alwaysExits stmt }
end

def scheduleBlock?
    (pinned : LiveSet) (layout : Locals.Layout)
    (source : Block) (facts : AllocationLivenessFacts.Region) :
    Option Region :=
  scheduleBlockFuel (AllocationLiveness.analysisFuel source)
    pinned layout source facts

theorem scheduleBlockFuel_entry_sound
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {source : Block} {facts : AllocationLivenessFacts.Region}
    {region : Region}
    (hSchedule :
      scheduleBlockFuel fuel pinned layout source facts = some region) :
    region.entry.source = layout ∧
      region.entry.live = required pinned (blockEntryLive source facts) ∧
      region.entry.schedule.ValidFor layout
        (required pinned (blockEntryLive source facts)) := by
  cases fuel with
  | zero => simp [scheduleBlockFuel] at hSchedule
  | succ fuel =>
      simp only [scheduleBlockFuel] at hSchedule
      by_cases hCover :
          covers layout (required pinned (blockEntryLive source facts))
      · rw [if_pos hCover] at hSchedule
        obtain ⟨entry, hEntry, hAfterEntry⟩ :=
          Option.bind_eq_some_iff.mp hSchedule
        obtain ⟨result, _hPoints, hResult⟩ :=
          Option.bind_eq_some_iff.mp hAfterEntry
        rcases result with ⟨points, finalLayout⟩
        have hRegion :
            ({ entry := entry
               points := points
               finalLayout := finalLayout } : Region) = region := by
          simpa only [Option.some.injEq] using hResult
        subst region
        exact Transition.build?_sound hEntry
      · rw [if_neg hCover] at hSchedule
        contradiction

theorem scheduleBlock?_entry_sound
    {pinned : LiveSet} {layout : Locals.Layout}
    {source : Block} {facts : AllocationLivenessFacts.Region}
    {region : Region}
    (hSchedule : scheduleBlock? pinned layout source facts = some region) :
    region.entry.source = layout ∧
      region.entry.live = required pinned (blockEntryLive source facts) ∧
      region.entry.schedule.ValidFor layout
        (required pinned (blockEntryLive source facts)) :=
  scheduleBlockFuel_entry_sound hSchedule

namespace Examples

def sequentialDeadSource : Block :=
  { stmts :=
      (List.range 32).map fun index =>
        .let_ ("dead_" ++ toString index)
          (.lit (EvmYul.UInt256.ofNat index)) }

def sequentialDeadFacts? : Option AllocationLivenessFacts.Region :=
  AllocationLivenessFacts.annotateBlock? { normal := ∅ }
    sequentialDeadSource

def sequentialDeadSchedule? : Option Region := do
  let facts ← sequentialDeadFacts?
  scheduleBlock? ∅ [] sequentialDeadSource facts

theorem sequentialDead_stackOnly :
    sequentialDeadSchedule?.map Region.finalLayout = some [] := by
  native_decide

def dormantCallSchedule? : Option Region := do
  let facts ←
    AllocationLivenessFacts.annotateBlock? { normal := ∅ }
      AllocationLiveness.Examples.callWithDormantValue
  scheduleBlock? ∅ ["sink", "result", "callerLive"]
    AllocationLiveness.Examples.callWithDormantValue facts

theorem dormantCall_schedule_succeeds :
    dormantCallSchedule?.isSome = true := by
  native_decide

end Examples

end StackSchedule
end Functions
end EvmCompiler
