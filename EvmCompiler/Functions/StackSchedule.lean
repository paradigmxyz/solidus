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

theorem scheduleStmtListFuel_cons_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {stmt : Stmt} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {scheduledPoints : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (stmt :: rest)
          (facts :: restFacts) = some (scheduledPoints, finalLayout)) :
    ∃ rawPoint,
      scheduleStmtFuel fuel pinned layout stmt facts = some rawPoint ∧
        ((rawPoint.fallsThrough = true ∧
            ∃ retain tail tailFinal,
              Transition.build? rawPoint.statementLayout
                  (required pinned
                    (nextLive facts.liveAfter rest restFacts)) =
                some retain ∧
              scheduleStmtListFuel fuel pinned retain.target rest restFacts =
                some (tail, tailFinal) ∧
              scheduledPoints =
                { rawPoint with retain? := some retain } :: tail ∧
              finalLayout = tailFinal) ∨
          (rawPoint.fallsThrough = false ∧
            scheduledPoints = [{ rawPoint with retain? := none }] ∧
            finalLayout = rawPoint.statementLayout)) := by
  simp only [scheduleStmtListFuel] at hSchedule
  by_cases hCover : covers layout (residentBefore stmt facts)
  · rw [if_pos hCover] at hSchedule
    obtain ⟨rawPoint, hPoint, hAfterPoint⟩ :=
      Option.bind_eq_some_iff.mp hSchedule
    refine ⟨rawPoint, hPoint, ?_⟩
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
  · rw [if_neg hCover] at hSchedule
    contradiction

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
  obtain ⟨rawPoint, _hRaw, hRegular | hAbrupt⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  · obtain ⟨_hFalls, retain, tail, _tailFinal,
        _hRetain, _hTail, hPoints, _hFinal⟩ := hRegular
    exact ⟨{ rawPoint with retain? := some retain }, tail, hPoints⟩
  · exact
      ⟨{ rawPoint with retain? := none }, [], hAbrupt.2.1⟩

theorem scheduleStmtListFuel_nil_components
    {fuel : Nat} {pinned : LiveSet} {layout finalLayout : Locals.Layout}
    {scheduledPoints : List Point}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout [] [] =
        some (scheduledPoints, finalLayout)) :
    scheduledPoints = [] ∧ finalLayout = layout := by
  simp [scheduleStmtListFuel] at hSchedule
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
  | zero => simp [scheduleStmtFuel] at hSchedule
  | succ fuel =>
      simp [scheduleStmtFuel, alwaysExits] at hSchedule
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
  | zero => simp [scheduleStmtFuel] at hSchedule
  | succ fuel =>
      by_cases hMem : name ∈ layout
      · simp [scheduleStmtFuel, hMem] at hSchedule
      · simp [scheduleStmtFuel, hMem] at hSchedule
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
  | zero => simp [scheduleStmtFuel] at hSchedule
  | succ fuel =>
      simp [scheduleStmtFuel, alwaysExits] at hSchedule
      subst point
      simp

theorem scheduleStmtListFuel_expr_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {expr : Expr 0} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.expr expr :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout)) :
    ∃ retain tailFinal,
      point.beforeLayout = layout ∧
        point.statementLayout = layout ∧
        point.retain? = some retain ∧ point.regions = [] ∧
        point.fallsThrough = true ∧
        Transition.build? layout
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        scheduleStmtListFuel fuel pinned retain.target rest restFacts =
          some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨rawPoint, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  have hShape := scheduleStmtFuel_expr_components hRaw
  rcases hShape with
    ⟨hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩
  rcases hCases with hRegular | hAbrupt
  · obtain ⟨_hFalls, retain, tail, tailFinal,
        hRetain, hTail, hPoints, hFinal⟩ := hRegular
    injection hPoints with hPoint hTailPoints
    subst point
    subst tail
    refine
      ⟨retain, tailFinal, ?_, ?_, rfl, ?_, by simpa using hFalls,
        ?_, hTail, hFinal⟩
    · simpa using hBefore
    · simpa using hStatement
    · simpa using hRegions
    · simpa [hStatement] using hRetain
  · rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1

theorem scheduleStmtListFuel_let_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {name : Name} {value : Expr 1} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.let_ name value :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout)) :
    ∃ retain tailFinal,
      name ∉ layout ∧ point.beforeLayout = layout ∧
        point.statementLayout = name :: layout ∧
        point.retain? = some retain ∧ point.regions = [] ∧
        point.fallsThrough = true ∧
        Transition.build? (name :: layout)
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        scheduleStmtListFuel fuel pinned retain.target rest restFacts =
          some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨rawPoint, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  have hShape := scheduleStmtFuel_let_components hRaw
  rcases hShape with
    ⟨hFresh, hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩
  rcases hCases with hRegular | hAbrupt
  · obtain ⟨_hFalls, retain, tail, tailFinal,
        hRetain, hTail, hPoints, hFinal⟩ := hRegular
    injection hPoints with hPoint hTailPoints
    subst point
    subst tail
    refine
      ⟨retain, tailFinal, hFresh, ?_, ?_, rfl, ?_,
        by simpa using hFalls, ?_, hTail, hFinal⟩
    · simpa using hBefore
    · simpa using hStatement
    · simpa using hRegions
    · simpa [hStatement] using hRetain
  · rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1

theorem scheduleStmtListFuel_assign_components
    {fuel : Nat} {pinned : LiveSet} {layout : Locals.Layout}
    {name : Name} {value : Expr 1} {rest : List Stmt}
    {facts : AllocationLivenessFacts.Point}
    {restFacts : List AllocationLivenessFacts.Point}
    {point : Point} {points : List Point} {finalLayout : Locals.Layout}
    (hSchedule :
      scheduleStmtListFuel fuel pinned layout (.assign name value :: rest)
          (facts :: restFacts) = some (point :: points, finalLayout)) :
    ∃ retain tailFinal,
      point.beforeLayout = layout ∧
        point.statementLayout = layout ∧
        point.retain? = some retain ∧ point.regions = [] ∧
        point.fallsThrough = true ∧
        Transition.build? layout
            (required pinned (nextLive facts.liveAfter rest restFacts)) =
          some retain ∧
        scheduleStmtListFuel fuel pinned retain.target rest restFacts =
          some (points, tailFinal) ∧
        finalLayout = tailFinal := by
  obtain ⟨rawPoint, hRaw, hCases⟩ :=
    scheduleStmtListFuel_cons_components hSchedule
  have hShape := scheduleStmtFuel_assign_components hRaw
  rcases hShape with
    ⟨hBefore, hStatement, _hNoRetain, hRegions, hFalls⟩
  rcases hCases with hRegular | hAbrupt
  · obtain ⟨_hFalls, retain, tail, tailFinal,
        hRetain, hTail, hPoints, hFinal⟩ := hRegular
    injection hPoints with hPoint hTailPoints
    subst point
    subst tail
    refine
      ⟨retain, tailFinal, ?_, ?_, rfl, ?_, by simpa using hFalls,
        ?_, hTail, hFinal⟩
    · simpa using hBefore
    · simpa using hStatement
    · simpa using hRegions
    · simpa [hStatement] using hRetain
  · rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1

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
