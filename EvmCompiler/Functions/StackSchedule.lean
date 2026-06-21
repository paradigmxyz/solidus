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
    exit? : Option Join := none
    finalLayout : Locals.Layout

  structure Point where
    order? : Option AllocationLayout.Ordering := none
    beforeLayout : Locals.Layout
    statementLayout : Locals.Layout
    exit? : Option Join := none
    retain? : Option Transition
    regions : List Region := []
    fallsThrough : Bool := true
end

structure ControlTargets where
  brk? : Option Locals.Layout := none
  cont? : Option Locals.Layout := none

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

def accessible (layout : Locals.Layout) (name : Name) : Bool :=
  match Locals.Layout.lookupDepth? name layout with
  | some depth => depth ≤ 17
  | none => false

def orderPriority (layout : Locals.Layout) (stmt : Stmt)
    (facts : AllocationLivenessFacts.Point) : List Name :=
  let dying :=
    layout.filter fun name => decide (name ∉ facts.liveAfter)
  let immediate :=
    AllocationLivenessFacts.Stmt.nextUse stmt ++ dying
  let accessibleFuture := facts.nextUse.filter (accessible layout)
  ((AllocationLivenessFacts.stableUnique
      (immediate ++ accessibleFuture)).filter
        fun name => decide (name ∈ layout)).take 16

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
  def scheduleBlockFuelWithTargets
      (targets : ControlTargets) (fuel : Nat)
      (pinned : LiveSet) (layout : Locals.Layout)
      (source : Block) (facts : AllocationLivenessFacts.Region) :
      Option Region :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
        let entryDemand := required pinned (blockEntryLive source facts)
        if covers layout entryDemand then
        let entry ← Transition.build? layout entryDemand
        let (points, finalLayout) ←
          scheduleStmtListFuelWithTargets targets fuel pinned entry.target
            source.stmts facts.points
        some { entry, points, finalLayout }
        else
          none

  def scheduleStmtListFuelWithTargets
      (targets : ControlTargets) (fuel : Nat)
      (pinned : LiveSet) (layout : Locals.Layout) :
      List Stmt → List AllocationLivenessFacts.Point →
        Option (List Point × Locals.Layout)
    | [], [] => some ([], layout)
    | stmt :: rest, facts :: restFacts => do
        let order ← Ordering.build? layout (orderPriority layout stmt facts)
        let orderedLayout := order.target
        if covers orderedLayout (residentBefore stmt facts) then
        let point ←
          scheduleStmtFuelWithTargets targets fuel pinned orderedLayout
            stmt facts
        let point := { point with order? := some order }
        if point.fallsThrough then
          let afterDemand :=
            required pinned (nextLive facts.liveAfter rest restFacts)
          if covers point.statementLayout afterDemand then
          let retain ← Transition.build? point.statementLayout afterDemand
          let point := { point with retain? := some retain }
          let (tail, finalLayout) ←
            scheduleStmtListFuelWithTargets targets fuel pinned retain.target
              rest restFacts
          some (point :: tail, finalLayout)
          else
            none
        else
          some ({ point with retain? := none } :: [], point.statementLayout)
        else
          none
    | _, _ => none

  def scheduleCaseRegionsFuelWithTargets
      (targets : ControlTargets) (fuel : Nat)
      (pinned : LiveSet) (layout : Locals.Layout) :
      List (Word × Block) → List AllocationLivenessFacts.Region →
        Option (List Region)
    | [], [] => some []
    | (_, body) :: rest, facts :: restFacts => do
        let head ←
          scheduleBlockFuelWithTargets targets fuel pinned layout body facts
        let exit ← Join.build? head.finalLayout layout
        let head := { head with exit? := some exit, finalLayout := layout }
        let tail ←
          scheduleCaseRegionsFuelWithTargets targets fuel pinned layout
            rest restFacts
        some (head :: tail)
    | _, _ => none

  def scheduleDefaultRegionFuelWithTargets
      (targets : ControlTargets) (fuel : Nat)
      (pinned : LiveSet) (layout : Locals.Layout) :
      Option Block → List AllocationLivenessFacts.Region →
        Option (List Region)
    | none, [] => some []
    | some body, [facts] => do
        let region ←
          scheduleBlockFuelWithTargets targets fuel pinned layout body facts
        let exit ← Join.build? region.finalLayout layout
        let region :=
          { region with exit? := some exit, finalLayout := layout }
        some [region]
    | _, _ => none

  def scheduleStmtFuelWithTargets
      (targets : ControlTargets) (fuel : Nat)
      (pinned : LiveSet) (layout : Locals.Layout)
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
                { order? := none
                  beforeLayout := layout
                  statementLayout := name :: layout
                  retain? := none }
        | .block body =>
            match facts.regions with
            | [bodyFacts] => do
                let region ←
                  scheduleBlockFuelWithTargets targets fuel
                    (layoutSet layout) layout
                    body bodyFacts
                let exit ← Join.build? region.finalLayout layout
                let region :=
                  { region with exit? := some exit, finalLayout := layout }
                some
                  { order? := none
                    beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    regions := [region] }
            | _ => none
        | .if_ _ body =>
            match facts.regions with
            | [bodyFacts] => do
                let region ←
                  scheduleBlockFuelWithTargets targets fuel
                    (layoutSet layout) layout
                    body bodyFacts
                let exit ← Join.build? region.finalLayout layout
                let region :=
                  { region with exit? := some exit, finalLayout := layout }
                some
                  { order? := none
                    beforeLayout := layout
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
              scheduleCaseRegionsFuelWithTargets targets fuel
                branchProtected layout
                cases caseFacts
            let defaultRegions ←
              scheduleDefaultRegionFuelWithTargets targets fuel
                branchProtected layout
                defaultBody defaultFacts
            some
              { order? := none
                beforeLayout := layout
                statementLayout := layout
                retain? := none
                regions := caseRegions ++ defaultRegions }
        | .for_ init _ post body =>
            match facts.regions, facts.loop? with
            | [initFacts, postFacts, bodyFacts], some _loop => do
                let outerProtected := layoutSet layout
                let initRegion ←
                  scheduleBlockFuelWithTargets targets fuel outerProtected
                    layout init initFacts
                let baseline := initRegion.finalLayout
                let loopProtected := layoutSet baseline
                let loopTargets : ControlTargets :=
                  { targets with
                    brk? := some baseline
                    cont? := some baseline }
                let postRegion ←
                  scheduleBlockFuelWithTargets loopTargets fuel loopProtected
                    baseline post postFacts
                let bodyRegion ←
                  scheduleBlockFuelWithTargets loopTargets fuel loopProtected
                    baseline body bodyFacts
                let postExit ← Join.build? postRegion.finalLayout baseline
                let bodyExit ← Join.build? bodyRegion.finalLayout baseline
                let postRegion :=
                  { postRegion with
                      exit? := some postExit, finalLayout := baseline }
                let bodyRegion :=
                  { bodyRegion with
                      exit? := some bodyExit, finalLayout := baseline }
                some
                  { order? := none
                    beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    regions := [initRegion, postRegion, bodyRegion] }
            | _, _ => none
        | .brk =>
            match targets.brk? with
            | none =>
                some
                  { order? := none
                    beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    fallsThrough := false }
            | some target => do
                let exit ← Join.build? layout target
                some
                  { order? := none
                    beforeLayout := layout
                    statementLayout := target
                    exit? := some exit
                    retain? := none
                    fallsThrough := false }
        | .cont =>
            match targets.cont? with
            | none =>
                some
                  { order? := none
                    beforeLayout := layout
                    statementLayout := layout
                    retain? := none
                    fallsThrough := false }
            | some target => do
                let exit ← Join.build? layout target
                some
                  { order? := none
                    beforeLayout := layout
                    statementLayout := target
                    exit? := some exit
                    retain? := none
                    fallsThrough := false }
        | _ =>
            some
              { order? := none
                beforeLayout := layout
                statementLayout := layout
                retain? := none
                fallsThrough := !alwaysExits stmt }
end

def scheduleBlockFuel
    (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout)
    (source : Block) (facts : AllocationLivenessFacts.Region) :
    Option Region :=
  scheduleBlockFuelWithTargets {} fuel pinned layout source facts

def scheduleStmtListFuel
    (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout)
    (stmts : List Stmt) (facts : List AllocationLivenessFacts.Point) :
    Option (List Point × Locals.Layout) :=
  scheduleStmtListFuelWithTargets {} fuel pinned layout stmts facts

def scheduleStmtFuel
    (fuel : Nat) (pinned : LiveSet) (layout : Locals.Layout)
    (stmt : Stmt) (facts : AllocationLivenessFacts.Point) : Option Point :=
  scheduleStmtFuelWithTargets {} fuel pinned layout stmt facts

def scheduleBlock?
    (pinned : LiveSet) (layout : Locals.Layout)
    (source : Block) (facts : AllocationLivenessFacts.Region) :
    Option Region :=
  scheduleBlockFuel (AllocationLiveness.analysisFuel source)
    pinned layout source facts

/--
Successful scheduling of a block exposes the checked entry transition and the
recursively scheduled statement list owned by this pass.
-/
theorem scheduleBlockFuelWithTargets_components
    {targets : ControlTargets} {fuel : Nat}
    {pinned : LiveSet} {layout : Locals.Layout}
    {source : Block} {facts : AllocationLivenessFacts.Region}
    {region : Region}
    (hSchedule :
      scheduleBlockFuelWithTargets targets fuel pinned layout source facts =
        some region) :
    ∃ entry points finalLayout,
      Transition.build? layout
          (required pinned (blockEntryLive source facts)) = some entry ∧
        scheduleStmtListFuelWithTargets targets (fuel - 1) pinned entry.target
            source.stmts facts.points = some (points, finalLayout) ∧
        region.entry = entry ∧ region.points = points ∧
        region.exit? = none ∧ region.finalLayout = finalLayout := by
  cases fuel with
  | zero =>
      simp [scheduleBlockFuelWithTargets] at hSchedule
  | succ fuel =>
      simp only [scheduleBlockFuelWithTargets] at hSchedule
      by_cases hCover :
          covers layout (required pinned (blockEntryLive source facts))
      · rw [if_pos hCover] at hSchedule
        obtain ⟨entry, hEntry, hAfterEntry⟩ :=
          Option.bind_eq_some_iff.mp hSchedule
        obtain ⟨result, hPoints, hResult⟩ :=
          Option.bind_eq_some_iff.mp hAfterEntry
        rcases result with ⟨points, finalLayout⟩
        have hRegion :
            ({ entry := entry
               points := points
               finalLayout := finalLayout } : Region) = region := by
          simpa only [Option.some.injEq] using hResult
        subst region
        exact ⟨entry, points, finalLayout, hEntry, by simpa using hPoints,
          rfl, rfl, rfl, rfl⟩
      · rw [if_neg hCover] at hSchedule
        contradiction

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
  | zero =>
      simp [scheduleBlockFuel, scheduleBlockFuelWithTargets] at hSchedule
  | succ fuel =>
      simp only [scheduleBlockFuel, scheduleBlockFuelWithTargets] at hSchedule
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

theorem scheduleStmtListFuelWithTargets_cons_components
    {targets : ControlTargets} {fuel : Nat}
    {pinned : LiveSet} {layout : Locals.Layout}
    {stmt : Stmt} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {scheduledPoints : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuelWithTargets targets fuel pinned layout (stmt :: rest)
          (facts :: restFacts) = some (scheduledPoints, finalLayout)) :
    ∃ order rawPoint,
      Ordering.build? layout (orderPriority layout stmt facts) = some order ∧
      scheduleStmtFuelWithTargets targets fuel pinned order.target stmt facts =
          some rawPoint ∧
        ((rawPoint.fallsThrough = true ∧
            ∃ retain tail tailFinal,
              Transition.build? rawPoint.statementLayout
                  (required pinned
                    (nextLive facts.liveAfter rest restFacts)) =
                some retain ∧
              scheduleStmtListFuelWithTargets targets fuel pinned
                  retain.target rest restFacts = some (tail, tailFinal) ∧
              scheduledPoints =
                { rawPoint with order? := some order, retain? := some retain } ::
                  tail ∧
              finalLayout = tailFinal) ∨
          (rawPoint.fallsThrough = false ∧
            scheduledPoints =
              [{ rawPoint with order? := some order, retain? := none }] ∧
            finalLayout = rawPoint.statementLayout)) := by
  simp only [scheduleStmtListFuelWithTargets] at hSchedule
  obtain ⟨order, hOrder, hAfterOrder⟩ :=
    Option.bind_eq_some_iff.mp hSchedule
  by_cases hCover : covers order.target (residentBefore stmt facts)
  · rw [if_pos hCover] at hAfterOrder
    obtain ⟨rawPoint, hPoint, hAfterPoint⟩ :=
      Option.bind_eq_some_iff.mp hAfterOrder
    refine ⟨order, rawPoint, hOrder, hPoint, ?_⟩
    cases hFalls : rawPoint.fallsThrough with
    | false =>
        rw [hFalls] at hAfterPoint
        have hResult := Option.some.inj hAfterPoint
        injection hResult with hPoints hFinal
        exact .inr ⟨rfl, hPoints.symm, hFinal.symm⟩
    | true =>
        rw [hFalls] at hAfterPoint
        by_cases hAfterCover :
            covers rawPoint.statementLayout
              (required pinned
                (nextLive facts.liveAfter rest restFacts))
        · rw [if_pos hAfterCover] at hAfterPoint
          obtain ⟨retain, hRetain, hAfterRetain⟩ :=
            Option.bind_eq_some_iff.mp hAfterPoint
          obtain ⟨result, hTail, hResult⟩ :=
            Option.bind_eq_some_iff.mp hAfterRetain
          rcases result with ⟨tail, tailFinal⟩
          have hPair := Option.some.inj hResult
          injection hPair with hPoints hFinal
          exact
            .inl ⟨rfl, retain, tail, tailFinal, hRetain, hTail,
              hPoints.symm, hFinal.symm⟩
        · rw [if_neg hAfterCover] at hAfterPoint
          contradiction
  · rw [if_neg hCover] at hAfterOrder
    contradiction

theorem scheduleStmtListFuelWithTargets_cons_fallsThrough_components
    {targets : ControlTargets} {fuel : Nat}
    {pinned : LiveSet} {layout : Locals.Layout}
    {stmt : Stmt} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuelWithTargets targets fuel pinned layout (stmt :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout))
    (hFalls :
      ∀ {before rawPoint},
        scheduleStmtFuelWithTargets targets fuel pinned before stmt facts =
            some rawPoint →
          rawPoint.fallsThrough = true) :
    ∃ order rawPoint retain tailFinal,
      Ordering.build? layout (orderPriority layout stmt facts) = some order ∧
        scheduleStmtFuelWithTargets targets fuel pinned order.target stmt facts =
          some rawPoint ∧
        rawPoint.fallsThrough = true ∧
        Transition.build? rawPoint.statementLayout
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        point =
          { rawPoint with order? := some order, retain? := some retain } ∧
        scheduleStmtListFuelWithTargets targets fuel pinned retain.target rest
            restFacts = some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuelWithTargets_cons_components hSchedule
  have hRawFalls : rawPoint.fallsThrough = true := by
    apply hFalls
    simpa using hRaw
  have hRegular := hCases.resolve_right (by
    intro hAbrupt
    rw [hRawFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1)
  obtain ⟨_hFalls, retain, tail, tailFinal, hRetain, hTail, hPoints,
      hFinal⟩ := hRegular
  injection hPoints with hPoint hTailPoints
  subst point
  subst tail
  exact ⟨order, rawPoint, retain, tailFinal, hOrder, hRaw, hRawFalls,
    hRetain, rfl, hTail, hFinal⟩

theorem scheduleStmtListFuel_cons_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {stmt : Stmt} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {scheduledPoints : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (stmt :: rest)
          (facts :: restFacts) = some (scheduledPoints, finalLayout)) :
    ∃ order rawPoint,
      Ordering.build? layout (orderPriority layout stmt facts) = some order ∧
      scheduleStmtFuel fuel pinned order.target stmt facts = some rawPoint ∧
        ((rawPoint.fallsThrough = true ∧
            ∃ retain tail tailFinal,
              Transition.build? rawPoint.statementLayout
                  (required pinned
                    (nextLive facts.liveAfter rest restFacts)) =
                some retain ∧
              scheduleStmtListFuel fuel pinned retain.target rest restFacts =
                some (tail, tailFinal) ∧
              scheduledPoints =
                { rawPoint with order? := some order, retain? := some retain } ::
                  tail ∧
              finalLayout = tailFinal) ∨
          (rawPoint.fallsThrough = false ∧
            scheduledPoints =
              [{ rawPoint with order? := some order, retain? := none }] ∧
            finalLayout = rawPoint.statementLayout)) := by
  simpa [scheduleStmtListFuel, scheduleStmtFuel] using
    (scheduleStmtListFuelWithTargets_cons_components
      (targets := {}) hSchedule)

theorem scheduleStmtListFuel_cons_nonempty
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {stmt : Stmt} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {scheduledPoints : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (stmt :: rest)
          (facts :: restFacts) = some (scheduledPoints, finalLayout)) :
    ∃ point points, scheduledPoints = point :: points := by
  obtain ⟨order, rawPoint, _hOrder, _hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  cases hFalls : rawPoint.fallsThrough with
  | false =>
      have hAbrupt := hCases.resolve_left (by
        intro hRegular
        rw [hFalls] at hRegular
        exact Bool.noConfusion hRegular.1)
      exact
        ⟨{ rawPoint with order? := some order, retain? := none },
          [], hAbrupt.2.1⟩
  | true =>
      have hRegular := hCases.resolve_right (by
        intro hAbrupt
        rw [hFalls] at hAbrupt
        exact Bool.noConfusion hAbrupt.1)
      obtain ⟨_hFalls, retain, tail, _tailFinal,
          _hRetain, _hTail, hPoints, _hFinal⟩ := hRegular
      exact
        ⟨{ rawPoint with order? := some order, retain? := some retain },
          tail, hPoints⟩

theorem scheduleStmtListFuel_nil_components
    {fuel : Nat} {pinned : LiveSet} {layout finalLayout : Locals.Layout}
    {scheduledPoints : List Point}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout [] [] =
        some (scheduledPoints, finalLayout)) :
    scheduledPoints = [] ∧ finalLayout = layout := by
  simp [scheduleStmtListFuel, scheduleStmtListFuelWithTargets] at hSchedule
  exact ⟨hSchedule.1, hSchedule.2.symm⟩

theorem scheduleStmtFuel_expr_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {expr : Expr 0} {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuel fuel pinned layout (.expr expr) facts = some point) :
    point.beforeLayout = layout ∧
      point.statementLayout = layout ∧
      point.retain? = none ∧ point.regions = [] ∧
      point.fallsThrough = true := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets, alwaysExits]
        at hSchedule
      subst point
      simp

theorem scheduleStmtFuel_let_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {name : Name} {value : Expr 1}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuel fuel pinned layout (.let_ name value) facts =
        some point) :
    name ∉ layout ∧ point.beforeLayout = layout ∧
      point.statementLayout = name :: layout ∧
      point.retain? = none ∧ point.regions = [] ∧
      point.fallsThrough = true := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      by_cases hMem : name ∈ layout
      · simp [scheduleStmtFuel, scheduleStmtFuelWithTargets, hMem] at hSchedule
      · simp [scheduleStmtFuel, scheduleStmtFuelWithTargets, hMem] at hSchedule
        subst point
        exact ⟨hMem, rfl, rfl, rfl, rfl, rfl⟩

theorem scheduleStmtFuel_assign_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {name : Name} {value : Expr 1}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuel fuel pinned layout (.assign name value) facts =
        some point) :
    point.beforeLayout = layout ∧
      point.statementLayout = layout ∧
      point.retain? = none ∧ point.regions = [] ∧
      point.fallsThrough = true := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets, alwaysExits]
        at hSchedule
      subst point
      simp

theorem scheduleStmtFuel_terminal_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {kind : Assembly.HaltKind}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuel fuel pinned layout (.terminal kind) facts =
        some point) :
    point.beforeLayout = layout ∧
      point.statementLayout = layout ∧
      point.retain? = none ∧ point.regions = [] ∧
      point.fallsThrough = false := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets, alwaysExits]
        at hSchedule
      subst point
      simp

theorem scheduleStmtFuel_terminalArgs_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {kind : Assembly.HaltKind} {args : Locals.ExprSeq kind.argCount}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuel fuel pinned layout (.terminalArgs kind args) facts =
        some point) :
    point.beforeLayout = layout ∧
      point.statementLayout = layout ∧
      point.retain? = none ∧ point.regions = [] ∧
      point.fallsThrough = false := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      simp [scheduleStmtFuel, scheduleStmtFuelWithTargets, alwaysExits]
        at hSchedule
      subst point
      simp

theorem scheduleStmtFuelWithTargets_brk_components
    {targets : ControlTargets} {fuel : Nat} {pinned : LiveSet}
    {layout target : Locals.Layout}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hTarget : targets.brk? = some target)
    (hSchedule :
      scheduleStmtFuelWithTargets targets fuel pinned layout .brk facts =
        some point) :
    ∃ exit,
      Join.build? layout target = some exit ∧
        point.beforeLayout = layout ∧
        point.statementLayout = target ∧
        point.exit? = some exit ∧ point.retain? = none ∧
        point.regions = [] ∧ point.fallsThrough = false := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      cases hExit : Join.build? layout target with
      | none =>
          simp [scheduleStmtFuelWithTargets, hTarget, hExit] at hSchedule
      | some exit =>
          simp [scheduleStmtFuelWithTargets, hTarget, hExit] at hSchedule
          subst point
          exact ⟨exit, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scheduleStmtFuelWithTargets_cont_components
    {targets : ControlTargets} {fuel : Nat} {pinned : LiveSet}
    {layout target : Locals.Layout}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hTarget : targets.cont? = some target)
    (hSchedule :
      scheduleStmtFuelWithTargets targets fuel pinned layout .cont facts =
        some point) :
    ∃ exit,
      Join.build? layout target = some exit ∧
        point.beforeLayout = layout ∧
        point.statementLayout = target ∧
        point.exit? = some exit ∧ point.retain? = none ∧
        point.regions = [] ∧ point.fallsThrough = false := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      cases hExit : Join.build? layout target with
      | none =>
          simp [scheduleStmtFuelWithTargets, hTarget, hExit] at hSchedule
      | some exit =>
          simp [scheduleStmtFuelWithTargets, hTarget, hExit] at hSchedule
          subst point
          exact ⟨exit, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scheduleStmtFuelWithTargets_block_components
    {targets : ControlTargets} {fuel : Nat} {pinned : LiveSet}
    {layout : Locals.Layout} {body : Block}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuelWithTargets targets fuel pinned layout (.block body)
          facts = some point) :
    ∃ bodyFacts rawRegion exit,
      facts.regions = [bodyFacts] ∧
        scheduleBlockFuelWithTargets targets (fuel - 1) (layoutSet layout)
            layout body bodyFacts = some rawRegion ∧
        Join.build? rawRegion.finalLayout layout = some exit ∧
        point.beforeLayout = layout ∧ point.statementLayout = layout ∧
        point.exit? = none ∧ point.retain? = none ∧
        point.regions =
          [{ rawRegion with exit? := some exit, finalLayout := layout }] ∧
        point.fallsThrough = true := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      cases hRegions : facts.regions with
      | nil =>
          simp [scheduleStmtFuelWithTargets, hRegions] at hSchedule
      | cons bodyFacts rest =>
          cases rest with
          | cons next tail =>
              simp [scheduleStmtFuelWithTargets, hRegions] at hSchedule
          | nil =>
              cases hRegion :
                  scheduleBlockFuelWithTargets targets fuel
                    (layoutSet layout) layout body bodyFacts with
              | none =>
                  simp [scheduleStmtFuelWithTargets, hRegions, hRegion]
                    at hSchedule
              | some rawRegion =>
                  cases hExit : Join.build? rawRegion.finalLayout layout with
                  | none =>
                      simp [scheduleStmtFuelWithTargets, hRegions, hRegion,
                        hExit] at hSchedule
                  | some exit =>
                      simp [scheduleStmtFuelWithTargets, hRegions, hRegion,
                        hExit] at hSchedule
                      subst point
                      exact
                        ⟨bodyFacts, rawRegion, exit, rfl, by simpa using hRegion,
                          hExit, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scheduleStmtFuelWithTargets_if_components
    {targets : ControlTargets} {fuel : Nat} {pinned : LiveSet}
    {layout : Locals.Layout} {cond : Expr 1} {body : Block}
    {facts : AllocationLivenessFacts.Point} {point : Point}
    (hSchedule :
      scheduleStmtFuelWithTargets targets fuel pinned layout (.if_ cond body)
          facts = some point) :
    ∃ bodyFacts rawRegion exit,
      facts.regions = [bodyFacts] ∧
        scheduleBlockFuelWithTargets targets (fuel - 1) (layoutSet layout)
            layout body bodyFacts = some rawRegion ∧
        Join.build? rawRegion.finalLayout layout = some exit ∧
        point.beforeLayout = layout ∧ point.statementLayout = layout ∧
        point.exit? = none ∧ point.retain? = none ∧
        point.regions =
          [{ rawRegion with exit? := some exit, finalLayout := layout }] ∧
        point.fallsThrough = true := by
  cases fuel with
  | zero =>
      simp [scheduleStmtFuelWithTargets] at hSchedule
  | succ fuel =>
      cases hRegions : facts.regions with
      | nil =>
          simp [scheduleStmtFuelWithTargets, hRegions] at hSchedule
      | cons bodyFacts rest =>
          cases rest with
          | cons next tail =>
              simp [scheduleStmtFuelWithTargets, hRegions] at hSchedule
          | nil =>
              cases hRegion :
                  scheduleBlockFuelWithTargets targets fuel
                    (layoutSet layout) layout body bodyFacts with
              | none =>
                  simp [scheduleStmtFuelWithTargets, hRegions, hRegion]
                    at hSchedule
              | some rawRegion =>
                  cases hExit : Join.build? rawRegion.finalLayout layout with
                  | none =>
                      simp [scheduleStmtFuelWithTargets, hRegions, hRegion,
                        hExit] at hSchedule
                  | some exit =>
                      simp [scheduleStmtFuelWithTargets, hRegions, hRegion,
                        hExit] at hSchedule
                      subst point
                      exact
                        ⟨bodyFacts, rawRegion, exit, rfl, by simpa using hRegion,
                          hExit, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scheduleStmtListFuelWithTargets_brk_components
    {targets : ControlTargets} {fuel : Nat} {pinned : LiveSet}
    {layout target : Locals.Layout} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hTarget : targets.brk? = some target)
    (hSchedule :
      scheduleStmtListFuelWithTargets targets fuel pinned layout
          (.brk :: rest) (facts :: restFacts) =
        some (point :: points, finalLayout)) :
    ∃ order exit,
      Ordering.build? layout (orderPriority layout .brk facts) = some order ∧
        Join.build? order.target target = some exit ∧
        point.order? = some order ∧ point.beforeLayout = order.target ∧
        point.statementLayout = target ∧ point.exit? = some exit ∧
        point.retain? = none ∧ point.regions = [] ∧
        point.fallsThrough = false ∧ points = [] ∧ finalLayout = target := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuelWithTargets_cons_components hSchedule
  obtain ⟨exit, hExit, hBefore, hStatement, hPointExit,
      hRetain, hRegions, hFalls⟩ :=
    scheduleStmtFuelWithTargets_brk_components hTarget hRaw
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1)
  obtain ⟨_hFalse, hPoints, hFinal⟩ := hAbrupt
  injection hPoints with hPoint hTail
  subst point
  subst points
  refine ⟨order, exit, hOrder, hExit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rfl
  · exact hBefore
  · exact hStatement
  · exact hPointExit
  · rfl
  · exact hRegions
  · exact hFalls
  · rwa [hStatement] at hFinal

theorem scheduleStmtListFuelWithTargets_cont_components
    {targets : ControlTargets} {fuel : Nat} {pinned : LiveSet}
    {layout target : Locals.Layout} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hTarget : targets.cont? = some target)
    (hSchedule :
      scheduleStmtListFuelWithTargets targets fuel pinned layout
          (.cont :: rest) (facts :: restFacts) =
        some (point :: points, finalLayout)) :
    ∃ order exit,
      Ordering.build? layout (orderPriority layout .cont facts) = some order ∧
        Join.build? order.target target = some exit ∧
        point.order? = some order ∧ point.beforeLayout = order.target ∧
        point.statementLayout = target ∧ point.exit? = some exit ∧
        point.retain? = none ∧ point.regions = [] ∧
        point.fallsThrough = false ∧ points = [] ∧ finalLayout = target := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuelWithTargets_cons_components hSchedule
  obtain ⟨exit, hExit, hBefore, hStatement, hPointExit,
      hRetain, hRegions, hFalls⟩ :=
    scheduleStmtFuelWithTargets_cont_components hTarget hRaw
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1)
  obtain ⟨_hFalse, hPoints, hFinal⟩ := hAbrupt
  injection hPoints with hPoint hTail
  subst point
  subst points
  refine ⟨order, exit, hOrder, hExit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rfl
  · exact hBefore
  · exact hStatement
  · exact hPointExit
  · rfl
  · exact hRegions
  · exact hFalls
  · rwa [hStatement] at hFinal

theorem scheduleStmtListFuel_expr_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {expr : Expr 0} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.expr expr :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout)) :
    ∃ order retain tailFinal,
      Ordering.build? layout (orderPriority layout (.expr expr) facts) =
          some order ∧
        point.order? = some order ∧
        point.beforeLayout = order.target ∧
        point.statementLayout = order.target ∧
        point.retain? = some retain ∧ point.regions = [] ∧
        point.fallsThrough = true ∧
        Transition.build? order.target
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        scheduleStmtListFuel fuel pinned retain.target rest restFacts =
          some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  have hShape := scheduleStmtFuel_expr_components hRaw
  rcases hShape with
    ⟨hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩
  have hRegular := hCases.resolve_right (by
    intro hAbrupt
    rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1)
  obtain ⟨_hFalls, retain, tail, tailFinal,
      hRetain, hTail, hPoints, hFinal⟩ := hRegular
  injection hPoints with hPoint hTailPoints
  subst point
  subst tail
  refine
    ⟨order, retain, tailFinal, hOrder, rfl, ?_, ?_, rfl, ?_,
      by simpa using hFalls,
      ?_, hTail, hFinal⟩
  · simpa using hBefore
  · simpa using hStatement
  · simpa using hRegions
  · simpa [hStatement] using hRetain

theorem scheduleStmtListFuel_let_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {name : Name} {value : Expr 1} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.let_ name value :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout)) :
    ∃ order retain tailFinal,
      Ordering.build? layout (orderPriority layout (.let_ name value) facts) =
          some order ∧
        point.order? = some order ∧
        name ∉ order.target ∧ point.beforeLayout = order.target ∧
        point.statementLayout = name :: order.target ∧
        point.retain? = some retain ∧ point.regions = [] ∧
        point.fallsThrough = true ∧
        Transition.build? (name :: order.target)
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        scheduleStmtListFuel fuel pinned retain.target rest restFacts =
          some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  have hShape := scheduleStmtFuel_let_components hRaw
  rcases hShape with
    ⟨hFresh, hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩
  have hRegular := hCases.resolve_right (by
    intro hAbrupt
    rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1)
  obtain ⟨_hFalls, retain, tail, tailFinal,
      hRetain, hTail, hPoints, hFinal⟩ := hRegular
  injection hPoints with hPoint hTailPoints
  subst point
  subst tail
  refine
    ⟨order, retain, tailFinal, hOrder, rfl, hFresh, ?_, ?_, rfl, ?_,
      by simpa using hFalls, ?_, hTail, hFinal⟩
  · simpa using hBefore
  · simpa using hStatement
  · simpa using hRegions
  · simpa [hStatement] using hRetain

theorem scheduleStmtListFuel_assign_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {name : Name} {value : Expr 1} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.assign name value :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout)) :
    ∃ order retain tailFinal,
      Ordering.build? layout (orderPriority layout (.assign name value) facts) =
          some order ∧
        point.order? = some order ∧
        point.beforeLayout = order.target ∧
        point.statementLayout = order.target ∧
        point.retain? = some retain ∧ point.regions = [] ∧
        point.fallsThrough = true ∧
        Transition.build? order.target
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        scheduleStmtListFuel fuel pinned retain.target rest restFacts =
          some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  have hShape := scheduleStmtFuel_assign_components hRaw
  rcases hShape with
    ⟨hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩
  have hRegular := hCases.resolve_right (by
    intro hAbrupt
    rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1)
  obtain ⟨_hFalls, retain, tail, tailFinal,
      hRetain, hTail, hPoints, hFinal⟩ := hRegular
  injection hPoints with hPoint hTailPoints
  subst point
  subst tail
  refine
    ⟨order, retain, tailFinal, hOrder, rfl, ?_, ?_, rfl, ?_,
      by simpa using hFalls,
      ?_, hTail, hFinal⟩
  · simpa using hBefore
  · simpa using hStatement
  · simpa using hRegions
  · simpa [hStatement] using hRetain

theorem scheduleStmtListFuel_terminal_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {kind : Assembly.HaltKind} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {scheduledPoints : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.terminal kind :: rest)
          (facts :: restFacts) = some (scheduledPoints, finalLayout)) :
    ∃ order point,
      Ordering.build? layout (orderPriority layout (.terminal kind) facts) =
          some order ∧
        scheduledPoints = [point] ∧ point.order? = some order ∧
        point.beforeLayout = order.target ∧
        point.statementLayout = order.target ∧ point.retain? = none ∧
        point.regions = [] ∧ point.fallsThrough = false ∧
        finalLayout = order.target := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  obtain ⟨hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩ :=
    scheduleStmtFuel_terminal_components hRaw
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1)
  obtain ⟨_hFalls, hPoints, hFinal⟩ := hAbrupt
  let point := { rawPoint with order? := some order, retain? := none }
  refine ⟨order, point, hOrder, hPoints, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simpa [point] using hBefore
  · simpa [point] using hStatement
  · simpa [point] using hRegions
  · simpa [point] using hFalls
  · simpa [hStatement] using hFinal

theorem scheduleStmtListFuel_terminalArgs_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {kind : Assembly.HaltKind} {args : Locals.ExprSeq kind.argCount}
    {rest : List Stmt} {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {scheduledPoints : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout
          (.terminalArgs kind args :: rest) (facts :: restFacts) =
        some (scheduledPoints, finalLayout)) :
    ∃ order point,
      Ordering.build? layout
          (orderPriority layout (.terminalArgs kind args) facts) = some order ∧
        scheduledPoints = [point] ∧ point.order? = some order ∧
        point.beforeLayout = order.target ∧
        point.statementLayout = order.target ∧ point.retain? = none ∧
        point.regions = [] ∧ point.fallsThrough = false ∧
        finalLayout = order.target := by
  obtain ⟨order, rawPoint, hOrder, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  obtain ⟨hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩ :=
    scheduleStmtFuel_terminalArgs_components hRaw
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1)
  obtain ⟨_hFalls, hPoints, hFinal⟩ := hAbrupt
  let point := { rawPoint with order? := some order, retain? := none }
  refine ⟨order, point, hOrder, hPoints, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simpa [point] using hBefore
  · simpa [point] using hStatement
  · simpa [point] using hRegions
  · simpa [point] using hFalls
  · simpa [hStatement] using hFinal

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
