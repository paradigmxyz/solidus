import EvmCompiler.Functions.StackLowering

/-!
Read-only diagnostics for the checked Functions stack allocator.

This module does not choose schedules or lower code. It summarizes the
compiler-owned liveness facts and calls the production scheduler, access
checker, and lowerer so large source programs can expose their first failing
boundary without changing the compiler interface.
-/

namespace EvmCompiler
namespace Functions
namespace StackDiagnostics

open AllocationLiveness
open AllocationLivenessFacts
open AllocationLayout

structure Metrics where
  points : Nat := 0
  peakLive : Nat := 0
  livePointsOver16 : Nat := 0
  joins : Nat := 0
  dormantCallSites : Nat := 0
  peakDormant : Nat := 0
  deriving DecidableEq, Repr

namespace Metrics

def combine (left right : Metrics) : Metrics :=
  { points := left.points + right.points
    peakLive := max left.peakLive right.peakLive
    livePointsOver16 := left.livePointsOver16 + right.livePointsOver16
    joins := left.joins + right.joins
    dormantCallSites := left.dormantCallSites + right.dormantCallSites
    peakDormant := max left.peakDormant right.peakDormant }

def point (facts : AllocationLivenessFacts.Point) : Metrics :=
  let live := max facts.liveBefore.card facts.liveAfter.card
  let dormant := facts.call?.map (fun call => call.liveAcross.card) |>.getD 0
  { points := 1
    peakLive := live
    livePointsOver16 := if 16 < live then 1 else 0
    joins := if facts.regions.isEmpty then 0 else 1
    dormantCallSites := if facts.call?.isSome then 1 else 0
    peakDormant := dormant }

mutual
  def regionFuel : Nat → AllocationLivenessFacts.Region → Metrics
    | 0, _ => {}
    | fuel + 1, facts =>
        let root : Metrics :=
          { peakLive := facts.liveIn.card
            livePointsOver16 := if 16 < facts.liveIn.card then 1 else 0 }
        combine root (pointsFuel fuel facts.points)

  def pointsFuel : Nat → List AllocationLivenessFacts.Point → Metrics
    | 0, _ => {}
    | _, [] => {}
    | fuel + 1, facts :: rest =>
        combine (pointFuel fuel facts) (pointsFuel fuel rest)

  def pointFuel (fuel : Nat)
      (facts : AllocationLivenessFacts.Point) : Metrics :=
    combine (point facts) (regionsFuel fuel facts.regions)

  def regionsFuel : Nat → List AllocationLivenessFacts.Region → Metrics
    | 0, _ => {}
    | _, [] => {}
    | fuel + 1, facts :: rest =>
        combine (regionFuel fuel facts) (regionsFuel fuel rest)
end

def block (source : Block) (facts : AllocationLivenessFacts.Region) : Metrics :=
  regionFuel (AllocationLiveness.analysisFuel source) facts

end Metrics

structure DiscardMetrics where
  transitions : Nat := 0
  successful : Nat := 0
  failures : Nat := 0
  oldSwaps : Nat := 0
  directSwaps : Nat := 0
  restoreFailures : Nat := 0
  restoreSwaps : Nat := 0
  discards : Nat := 0
  deriving Repr

namespace DiscardMetrics

def combine (left right : DiscardMetrics) : DiscardMetrics :=
  { transitions := left.transitions + right.transitions
    successful := left.successful + right.successful
    failures := left.failures + right.failures
    oldSwaps := left.oldSwaps + right.oldSwaps
    directSwaps := left.directSwaps + right.directSwaps
    restoreFailures := left.restoreFailures + right.restoreFailures
    restoreSwaps := left.restoreSwaps + right.restoreSwaps
    discards := left.discards + right.discards }

def transition (transition : AllocationLayout.Transition) : DiscardMetrics :=
  let oldSwaps :=
    transition.schedule.promotions.foldl
      (fun total promotion => total + (promotion.depth - 1)) 0
  match AllocationLayout.scheduleDiscards?
      transition.source transition.live with
  | none => { transitions := 1, failures := 1, oldSwaps := oldSwaps }
  | some schedule =>
      let directSwaps :=
        schedule.discards.foldl
          (fun total discard =>
            total + if discard.depth = 1 then 0 else 1) 0
      match AllocationLayout.Ordering.build?
          schedule.target transition.schedule.target with
      | none =>
          { transitions := 1
            successful := 1
            oldSwaps := oldSwaps
            directSwaps := directSwaps
            restoreFailures := 1
            discards := schedule.discards.length }
      | some restore =>
          let restoreSwaps :=
            restore.promotions.foldl
              (fun total promotion => total + (promotion.depth - 1)) 0
          { transitions := 1
            successful := 1
            oldSwaps := oldSwaps
            directSwaps := directSwaps
            restoreSwaps := restoreSwaps
            discards := schedule.discards.length }

def regularTransition
    (transition : AllocationLayout.RegularTransition) : DiscardMetrics :=
  let directSwaps :=
    transition.schedule.discards.foldl
      (fun total discard =>
        total + if discard.depth = 1 then 0 else 1) 0
  match AllocationLayout.Transition.build?
      transition.source transition.live with
  | none =>
      { transitions := 1
        successful := 1
        directSwaps := directSwaps
        restoreFailures := 1
        discards := transition.schedule.discards.length }
  | some old =>
      let oldSwaps :=
        old.schedule.promotions.foldl
          (fun total promotion => total + (promotion.depth - 1)) 0
      match AllocationLayout.Ordering.build?
          transition.target old.target with
      | none =>
          { transitions := 1
            successful := 1
            oldSwaps := oldSwaps
            directSwaps := directSwaps
            restoreFailures := 1
            discards := transition.schedule.discards.length }
      | some restore =>
          let restoreSwaps :=
            restore.promotions.foldl
              (fun total promotion => total + (promotion.depth - 1)) 0
          { transitions := 1
            successful := 1
            oldSwaps := oldSwaps
            directSwaps := directSwaps
            restoreSwaps := restoreSwaps
            discards := transition.schedule.discards.length }

def join (join : AllocationLayout.Join) : DiscardMetrics :=
  transition join.retain

mutual
  def regionFuel : Nat → StackSchedule.Region → DiscardMetrics
    | 0, _ => {}
    | fuel + 1, schedule =>
        combine (transition schedule.entry)
          (combine (pointsFuel fuel schedule.points)
            (schedule.exit?.map join |>.getD {}))

  def pointsFuel : Nat → List StackSchedule.Point → DiscardMetrics
    | 0, _ => {}
    | _, [] => {}
    | fuel + 1, point :: rest =>
        let here :=
          combine (point.retain?.map regularTransition |>.getD {})
            (combine (point.exit?.map join |>.getD {})
              (regionsFuel fuel point.regions))
        combine here (pointsFuel fuel rest)

  def regionsFuel : Nat → List StackSchedule.Region → DiscardMetrics
    | 0, _ => {}
    | _, [] => {}
    | fuel + 1, head :: rest =>
        combine (regionFuel fuel head) (regionsFuel fuel rest)
end

end DiscardMetrics

structure Failure where
  path : String
  phase : String
  reason : String
  deriving DecidableEq, Repr

def firstInaccessibleDead? (layout : Locals.Layout) (live : LiveSet) :
    Option (Name × Nat) :=
  let rec go : List Name → Option (Name × Nat)
    | [] => none
    | name :: rest =>
        match Locals.Layout.lookupDepth? name layout with
        | some depth => if 17 < depth then some (name, depth) else go rest
        | none => go rest
  go (AllocationLayout.dead layout live)

def transitionFailure (path phase : String)
    (layout : Locals.Layout) (live : LiveSet) : Failure :=
  match firstInaccessibleDead? layout live with
  | some (name, depth) =>
      { path, phase
        reason :=
          "dead value " ++ name ++ " is at depth " ++ toString depth ++
            " (maximum shuffle depth is 17)" }
  | none =>
      { path, phase
        reason :=
          "retained layout is not a cleanup suffix after checked promotions" }

def coverageFailure (path phase : String)
    (layout : Locals.Layout) (live : LiveSet) : Failure :=
  { path, phase
    reason :=
      "layout is missing " ++
        toString (live \ StackSchedule.layoutSet layout).card ++
        " demanded values" }

def scheduleStmtKind : Stmt → String
  | .expr _ => "expr"
  | .let_ _ _ => "let"
  | .assign _ _ => "assign"
  | .block _ => "block"
  | .if_ _ _ => "if"
  | .switch _ _ _ => "switch"
  | .for_ _ _ _ _ => "for"
  | .brk => "break"
  | .cont => "continue"
  | .leave => "leave"
  | .call _ _ _ => "call"
  | .terminal _ => "terminal"
  | .terminalArgs _ _ => "terminalArgs"

mutual
  def firstScheduleFailureBlockFuel
      (targets : StackSchedule.ControlTargets)
      (fuel : Nat) (path : String) (pinned : LiveSet)
      (layout : Locals.Layout) (source : Block)
      (facts : AllocationLivenessFacts.Region) : Option Failure :=
    match fuel with
    | 0 => some { path, phase := "schedule", reason := "scheduler fuel exhausted" }
    | fuel + 1 =>
        let demand := StackSchedule.required pinned
          (StackSchedule.blockEntryLive source facts)
        if !StackSchedule.covers layout demand then
          some (coverageFailure path "entry" layout demand)
        else
          match Transition.build? layout demand with
          | none => some (transitionFailure path "entry-transition" layout demand)
          | some entry =>
              firstScheduleFailureListFuel targets fuel path pinned entry.target
                source.stmts facts.points 0

  def firstScheduleFailureListFuel
      (targets : StackSchedule.ControlTargets)
      (fuel : Nat) (path : String) (pinned : LiveSet)
      (layout : Locals.Layout) :
      List Stmt → List AllocationLivenessFacts.Point → Nat → Option Failure
    | [], [], _ => none
    | source :: rest, facts :: restFacts, index =>
        let pointPath := path ++ "/stmt[" ++ toString index ++ "]"
        match Ordering.build? layout
            (StackSchedule.orderPriority layout source facts) with
        | none =>
            some
              { path := pointPath
                phase := "statement-ordering"
                reason := "next-use ordering cannot reach a requested value" }
        | some order =>
            let resident := StackSchedule.residentBefore source facts
            if !StackSchedule.covers order.target resident then
              some
                (coverageFailure pointPath "statement-entry"
                  order.target resident)
            else
              match StackSchedule.scheduleStmtFuelWithTargets targets fuel pinned order.target
                  source facts with
              | none =>
                  match source, facts.regions with
                  | .block body, [bodyFacts]
                  | .if_ _ body, [bodyFacts] =>
                      match firstScheduleFailureBlockFuel targets fuel
                          (pointPath ++ "/region[0]")
                          (StackSchedule.layoutSet order.target)
                          order.target body bodyFacts with
                      | some failure => some failure
                      | none =>
                          match StackSchedule.scheduleBlockFuelWithTargets
                              targets fuel
                              (StackSchedule.layoutSet order.target)
                              order.target body bodyFacts with
                          | some child =>
                              let failure :=
                                transitionFailure pointPath "statement-join"
                                  child.finalLayout
                                  (StackSchedule.layoutSet order.target)
                              some
                                { failure with
                                  reason :=
                                    scheduleStmtKind source ++ ": " ++
                                      failure.reason ++ "; child=" ++
                                      reprStr child.finalLayout ++ "; parent=" ++
                                      reprStr order.target }
                          | none =>
                              some
                                { path := pointPath
                                  phase := "statement-schedule"
                                  reason :=
                                    scheduleStmtKind source ++
                                      " child failed without a nested diagnostic" }
                  | .for_ init _ post body,
                      [initFacts, postFacts, bodyFacts] =>
                      let outerProtected := StackSchedule.layoutSet order.target
                      match StackSchedule.scheduleBlockFuelWithTargets {}
                          fuel outerProtected order.target init initFacts with
                      | none =>
                          firstScheduleFailureBlockFuel {} fuel
                            (pointPath ++ "/loop-init") outerProtected
                            order.target init initFacts
                      | some rawInit =>
                          let baseline :=
                            StackSchedule.loopBaseline order.target
                              rawInit.finalLayout
                          match AllocationLayout.Join.build?
                              rawInit.finalLayout baseline with
                          | none =>
                              some
                                { path := pointPath ++ "/loop-init"
                                  phase := "statement-join"
                                  reason :=
                                    "loop init cannot reach its canonical layout" }
                          | some _ =>
                              let loopProtected := StackSchedule.layoutSet baseline
                              match StackSchedule.scheduleBlockFuelWithTargets {}
                                  fuel loopProtected baseline post postFacts with
                              | none =>
                                  firstScheduleFailureBlockFuel {} fuel
                                    (pointPath ++ "/loop-post") loopProtected
                                    baseline post postFacts
                              | some postRegion =>
                                  match AllocationLayout.Join.build?
                                      postRegion.finalLayout baseline with
                                  | none =>
                                      some
                                        { path := pointPath ++ "/loop-post"
                                          phase := "statement-join"
                                          reason :=
                                            "loop post cannot restore its canonical layout" }
                                  | some _ =>
                                      let loopTargets : StackSchedule.ControlTargets :=
                                        { brk? := some baseline
                                          cont? := some baseline }
                                      match StackSchedule.scheduleBlockFuelWithTargets
                                          loopTargets fuel loopProtected baseline
                                          body bodyFacts with
                                      | none =>
                                          firstScheduleFailureBlockFuel loopTargets fuel
                                            (pointPath ++ "/loop-body") loopProtected
                                            baseline body bodyFacts
                                      | some bodyRegion =>
                                          match AllocationLayout.Join.build?
                                              bodyRegion.finalLayout baseline with
                                          | none =>
                                              some
                                                { path := pointPath ++ "/loop-body"
                                                  phase := "statement-join"
                                                  reason :=
                                                    "loop body cannot restore its canonical layout" }
                                          | some _ =>
                                              some
                                                { path := pointPath
                                                  phase := "statement-schedule"
                                                  reason :=
                                                    "loop scheduling failed after all child checks" }
                  | _, _ =>
                      some
                        { path := pointPath
                          phase := "statement-schedule"
                          reason :=
                            "scheduling " ++ scheduleStmtKind source ++
                              " or its structured children failed" }
              | some point =>
                  if point.fallsThrough then
                    let afterDemand := StackSchedule.required pinned
                      (StackSchedule.nextLive facts.liveAfter rest restFacts)
                    if !StackSchedule.covers point.statementLayout afterDemand then
                      some
                        (coverageFailure pointPath "fallthrough"
                          point.statementLayout afterDemand)
                    else
                      match Transition.build? point.statementLayout afterDemand with
                      | none =>
                          some
                            (transitionFailure pointPath "fallthrough-transition"
                              point.statementLayout afterDemand)
                      | some transition =>
                          firstScheduleFailureListFuel targets fuel path pinned
                            transition.target rest restFacts (index + 1)
                  else
                    none
    | _, _, index =>
        some
          { path := path ++ "/stmt[" ++ toString index ++ "]"
            phase := "fact-shape"
            reason := "source statements and liveness points have different lengths" }
end

def firstScheduleFailure? (path : String) (pinned : LiveSet)
    (layout : Locals.Layout) (source : Block)
    (facts : AllocationLivenessFacts.Region) : Option Failure :=
  if (StackSchedule.scheduleBlock? pinned layout source facts).isSome then
    none
  else
    firstScheduleFailureBlockFuel {} (AllocationLiveness.analysisFuel source)
      path pinned layout source facts

mutual
  def accessFailuresBlockFuel (fuel : Nat) (ctx : StackLowering.Ctx)
      (source : Block) (schedule : StackSchedule.Region) : Nat :=
    match fuel with
    | 0 => 1
    | fuel + 1 => accessFailuresListFuel fuel ctx source.stmts schedule.points

  def accessFailuresListFuel (fuel : Nat) (ctx : StackLowering.Ctx) :
      List Stmt → List StackSchedule.Point → Nat
    | source :: rest, point :: points =>
        match fuel with
        | 0 => 1
        | fuel + 1 =>
            accessFailuresPointFuel fuel ctx source point +
              accessFailuresListFuel fuel ctx rest points
    | [], [] => 0
    | _, _ => 1

  def accessFailuresPointFuel (fuel : Nat) (ctx : StackLowering.Ctx)
      (source : Stmt) (point : StackSchedule.Point) : Nat :=
    let own := if (StackLowering.pointAccess? ctx source point).isSome then 0 else 1
    let nested :=
      match source with
      | .block body | .if_ _ body =>
          match point.regions with
          | [region] => accessFailuresBlockFuel fuel ctx body region
          | _ => 1
      | .switch _ cases defaultBody =>
          let caseRegions := point.regions.take cases.length
          let defaultRegions := point.regions.drop cases.length
          accessFailuresCasesFuel fuel ctx cases caseRegions +
            accessFailuresDefaultFuel fuel ctx defaultBody defaultRegions
      | .for_ init _ post body =>
          match point.regions with
          | [initRegion, postRegion, bodyRegion] =>
              accessFailuresBlockFuel fuel ctx init initRegion +
                accessFailuresBlockFuel fuel ctx post postRegion +
                accessFailuresBlockFuel fuel ctx body bodyRegion
          | _ => 1
      | _ => 0
    own + nested

  def accessFailuresCasesFuel (fuel : Nat) (ctx : StackLowering.Ctx) :
      List (Word × Block) → List StackSchedule.Region → Nat
    | (_, body) :: rest, region :: regions =>
        match fuel with
        | 0 => 1
        | fuel + 1 =>
            accessFailuresBlockFuel fuel ctx body region +
              accessFailuresCasesFuel fuel ctx rest regions
    | [], [] => 0
    | _, _ => 1

  def accessFailuresDefaultFuel (fuel : Nat) (ctx : StackLowering.Ctx) :
      Option Block → List StackSchedule.Region → Nat
    | some body, [region] => accessFailuresBlockFuel fuel ctx body region
    | none, [] => 0
    | _, _ => 1
end

def accessFailuresBlock (ctx : StackLowering.Ctx)
    (source : Block) (schedule : StackSchedule.Region) : Nat :=
  accessFailuresBlockFuel (AllocationLiveness.analysisFuel source)
    ctx source schedule

def stmtKind : Stmt → String
  | .expr _ => "expression"
  | .let_ _ _ => "declaration"
  | .assign _ _ => "assignment"
  | .block _ => "block"
  | .if_ _ _ => "if-condition"
  | .switch _ _ _ => "switch-scrutinee"
  | .for_ _ _ _ _ => "loop-condition"
  | .brk => "break"
  | .cont => "continue"
  | .leave => "leave-results"
  | .call _ _ _ => "internal-call"
  | .terminal _ => "terminal"
  | .terminalArgs _ _ => "terminal-arguments"

mutual
  def firstAccessFailureBlockFuel (fuel : Nat) (path : String)
      (ctx : StackLowering.Ctx) (source : Block)
      (schedule : StackSchedule.Region) : Option Failure :=
    match fuel with
    | 0 =>
        some { path, phase := "access", reason := "diagnostic fuel exhausted" }
    | fuel + 1 =>
        firstAccessFailureListFuel fuel path ctx
          source.stmts schedule.points 0

  def firstAccessFailureListFuel (fuel : Nat) (path : String)
      (ctx : StackLowering.Ctx) :
      List Stmt → List StackSchedule.Point → Nat → Option Failure
    | source :: rest, point :: points, index =>
        let pointPath := path ++ "/stmt[" ++ toString index ++ "]"
        if (StackLowering.pointAccess? ctx source point).isNone then
          some
            { path := pointPath
              phase := "top16-access"
              reason :=
                stmtKind source ++ " failed in layout depth " ++
                  toString point.beforeLayout.length ++
                  "; layout=" ++ reprStr point.beforeLayout ++
                  "; expression-order=" ++
                    reprStr (AllocationLivenessFacts.Stmt.nextUse source) }
        else
          match firstAccessFailureNestedFuel fuel pointPath ctx source point with
          | some failure => some failure
          | none =>
              firstAccessFailureListFuel fuel path ctx rest points (index + 1)
    | [], [], _ => none
    | _, _, index =>
        some
          { path := path ++ "/stmt[" ++ toString index ++ "]"
            phase := "access-shape"
            reason := "source statements and schedule points have different lengths" }

  def firstAccessFailureNestedFuel (fuel : Nat) (path : String)
      (ctx : StackLowering.Ctx) (source : Stmt)
      (point : StackSchedule.Point) : Option Failure :=
    match fuel with
    | 0 =>
        some { path, phase := "access", reason := "diagnostic fuel exhausted" }
    | fuel + 1 =>
        match source with
        | .block body | .if_ _ body =>
            match point.regions with
            | [region] =>
                firstAccessFailureBlockFuel fuel (path ++ "/region[0]")
                  ctx body region
            | _ =>
                some { path, phase := "access-shape", reason := "expected one region" }
        | .switch _ cases defaultBody =>
            let caseRegions := point.regions.take cases.length
            let defaultRegions := point.regions.drop cases.length
            match firstAccessFailureCasesFuel fuel path ctx cases caseRegions 0 with
            | some failure => some failure
            | none =>
                firstAccessFailureDefaultFuel fuel path ctx
                  defaultBody defaultRegions
        | .for_ init _ post body =>
            match point.regions with
            | [initRegion, postRegion, bodyRegion] =>
                match firstAccessFailureBlockFuel fuel (path ++ "/loop-init")
                    ctx init initRegion with
                | some failure => some failure
                | none =>
                    match firstAccessFailureBlockFuel fuel (path ++ "/loop-post")
                        ctx post postRegion with
                    | some failure => some failure
                    | none =>
                        firstAccessFailureBlockFuel fuel (path ++ "/loop-body")
                          ctx body bodyRegion
            | _ =>
                some
                  { path, phase := "access-shape"
                    reason := "expected init, post, and body regions" }
        | _ => none

  def firstAccessFailureCasesFuel (fuel : Nat) (path : String)
      (ctx : StackLowering.Ctx) :
      List (Word × Block) → List StackSchedule.Region → Nat → Option Failure
    | (_, body) :: rest, region :: regions, index =>
        match firstAccessFailureBlockFuel fuel
            (path ++ "/case[" ++ toString index ++ "]") ctx body region with
        | some failure => some failure
        | none =>
            firstAccessFailureCasesFuel fuel path ctx rest regions (index + 1)
    | [], [], _ => none
    | _, _, _ =>
        some { path, phase := "access-shape", reason := "case regions differ" }

  def firstAccessFailureDefaultFuel (fuel : Nat) (path : String)
      (ctx : StackLowering.Ctx) :
      Option Block → List StackSchedule.Region → Option Failure
    | some body, [region] =>
        firstAccessFailureBlockFuel fuel (path ++ "/default") ctx body region
    | none, [] => none
    | _, _ =>
        some { path, phase := "access-shape", reason := "default region differs" }
end

def firstAccessFailure? (path : String) (ctx : StackLowering.Ctx)
    (source : Block) (schedule : StackSchedule.Region) : Option Failure :=
  firstAccessFailureBlockFuel (AllocationLiveness.analysisFuel source)
    path ctx source schedule

namespace NextUse

def unique : List Name → List Name
  | [] => []
  | name :: rest =>
      name :: (unique rest).filter fun candidate => decide (candidate ≠ name)

mutual
  def Expr.priority {results : Nat} : Functions.Expr results → List Name
    | .lit _ | .code _ => []
    | .var name => [name]
    | .prim _ args => ExprSeq.priority args

  def ExprSeq.priority {results : Nat} : Locals.ExprSeq results → List Name
    | .nil => []
    | .cons head tail => ExprSeq.priority tail ++ Expr.priority head
end

def statementPriority (ctx : StackLowering.Ctx) (source : Stmt) : List Name :=
  match source with
  | .leave => ExprSeq.priority (StackLowering.returnWords ctx.returns)
  | _ => StackAccess.Stmt.accessPriority source

mutual
  def allPriorityFuel (fuel : Nat) (ctx : StackLowering.Ctx)
      (source : Stmt) : List Name :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
        statementPriority ctx source ++
          match source with
          | .block body | .if_ _ body => blockPriorityFuel fuel ctx body
          | .switch _ cases defaultBody =>
              casesPriorityFuel fuel ctx cases ++
                (defaultBody.map (blockPriorityFuel fuel ctx) |>.getD [])
          | .for_ init _ post body =>
              blockPriorityFuel fuel ctx init ++
                blockPriorityFuel fuel ctx body ++
                blockPriorityFuel fuel ctx post
          | _ => []

  def blockPriorityFuel (fuel : Nat) (ctx : StackLowering.Ctx)
      (source : Block) : List Name :=
    futurePriorityFuel fuel ctx source.stmts

  def futurePriorityFuel (fuel : Nat) (ctx : StackLowering.Ctx) :
      List Stmt → List Name
    | [] => []
    | source :: rest =>
        match fuel with
        | 0 => []
        | fuel + 1 =>
            allPriorityFuel fuel ctx source ++
              futurePriorityFuel fuel ctx rest

  def casesPriorityFuel (fuel : Nat) (ctx : StackLowering.Ctx) :
      List (Word × Block) → List Name
    | [] => []
    | (_, body) :: rest =>
        match fuel with
        | 0 => []
        | fuel + 1 =>
            blockPriorityFuel fuel ctx body ++
              casesPriorityFuel fuel ctx rest
end

def futurePriority (ctx : StackLowering.Ctx) (sources : List Stmt) : List Name :=
  futurePriorityFuel
    (AllocationLiveness.analysisFuel { stmts := sources }) ctx sources

def accessible (layout : Locals.Layout) (name : Name) : Bool :=
  match Locals.Layout.lookupDepth? name layout with
  | some depth => depth ≤ 17
  | none => false

def priority (ctx : StackLowering.Ctx) (layout : Locals.Layout)
    (source : Stmt) (facts : AllocationLivenessFacts.Point)
    (rest : List Stmt) : List Name :=
  let immediate :=
    unique
      (statementPriority ctx source ++
        layout.filter fun name => decide (name ∉ facts.liveAfter))
  let future :=
    (unique (futurePriority ctx rest)).filter (accessible layout)
  ((unique (immediate ++ future)).filter
      fun name => decide (name ∈ layout)).take 16

def order? (ctx : StackLowering.Ctx) (layout : Locals.Layout)
    (source : Stmt) (facts : AllocationLivenessFacts.Point)
    (rest : List Stmt) :
    Option AllocationLayout.Ordering :=
  AllocationLayout.Ordering.build? layout
    (priority ctx layout source facts rest)

def firstOrderFailure? (layout : Locals.Layout) : List Name →
    Option (Name × Nat)
  | [] => none
  | name :: rest =>
      match Locals.Layout.lookupDepth? name layout with
      | none => some (name, 0)
      | some depth =>
          if 17 < depth then some (name, depth)
          else
            firstOrderFailure?
              (Locals.Layout.promoteAt (depth - 1) layout) rest

def commonPrefixLength : List Name → List Name → Nat
  | left :: leftRest, right :: rightRest =>
      if left = right then 1 + commonPrefixLength leftRest rightRest else 0
  | _, _ => 0

def commonSuffixLength (left right : Locals.Layout) : Nat :=
  commonPrefixLength left.reverse right.reverse

def restore (path : String) (layout expected : Locals.Layout) :
    Except Failure Locals.Layout := do
  let retained ←
    match Transition.build? layout (StackSchedule.layoutSet expected) with
    | some retained => pure retained
    | none =>
        throw
          (transitionFailure path "next-use-join-retain" layout
            (StackSchedule.layoutSet expected))
  let common := commonSuffixLength retained.target expected
  let desiredPrefix := expected.take (expected.length - common)
  let ordered ←
    match Ordering.build? retained.target desiredPrefix with
    | some ordered => pure ordered
    | none =>
        let reason :=
          match firstOrderFailure? retained.target desiredPrefix.reverse with
          | some (name, depth) =>
              "canonical value " ++ name ++ " is at depth " ++ toString depth
          | none => "canonical ordering construction failed"
        throw { path, phase := "next-use-join-order", reason }
  if ordered.target = expected then pure expected
  else
    throw
      { path, phase := "next-use-join-order"
        reason := "ordering did not produce the canonical layout" }

def directAccess? (ctx : StackLowering.Ctx) (layout : Locals.Layout) :
    Stmt → Option Unit
  | .expr expr => StackAccess.Expr.check? layout 0 expr
  | .let_ _ value => StackAccess.Expr.check? layout 0 value
  | .assign name value => StackAccess.assign? layout name value
  | .if_ condition _ => StackAccess.Expr.check? layout 0 condition
  | .switch scrutinee _ _ => StackAccess.Expr.check? layout 0 scrutinee
  | .leave =>
      StackAccess.ExprSeq.check? layout 0
        (StackLowering.returnWords ctx.returns)
  | .call targets _ args => StackAccess.call? layout targets args
  | .terminalArgs _ args => StackAccess.ExprSeq.check? layout 0 args
  | _ => some ()

mutual
  def blockFuel (fuel : Nat) (path : String) (ctx : StackLowering.Ctx)
      (pinned : LiveSet) (layout : Locals.Layout) (source : Block)
      (facts : AllocationLivenessFacts.Region) : Except Failure Locals.Layout :=
    match fuel with
    | 0 =>
        .error { path, phase := "next-use", reason := "scheduler fuel exhausted" }
    | fuel + 1 =>
        let demand := StackSchedule.required pinned
          (StackSchedule.blockEntryLive source facts)
        if !StackSchedule.covers layout demand then
          .error (coverageFailure path "next-use-entry" layout demand)
        else
          match Transition.build? layout demand with
          | none =>
              .error (transitionFailure path "next-use-entry" layout demand)
          | some entry =>
              listFuel fuel path ctx pinned entry.target
                source.stmts facts.points 0

  def listFuel (fuel : Nat) (path : String) (ctx : StackLowering.Ctx)
      (pinned : LiveSet) (layout : Locals.Layout) :
      List Stmt → List AllocationLivenessFacts.Point → Nat →
        Except Failure Locals.Layout
    | [], [], _ => .ok layout
    | source :: rest, facts :: restFacts, index => do
        let pointPath := path ++ "/stmt[" ++ toString index ++ "]"
        let ordering ←
          match order? ctx layout source facts rest with
          | some ordering => .ok ordering
          | none =>
              let reason :=
                match firstOrderFailure? layout
                    (priority ctx layout source facts rest).reverse with
                | some (name, depth) =>
                    "ordered value " ++ name ++ " is at depth " ++
                      toString depth
                | none => "ordering construction failed"
              .error
                { path := pointPath, phase := "next-use-order"
                  reason }
        let ordered := ordering.target
        let resident := StackSchedule.residentBefore source facts
        if !StackSchedule.covers ordered resident then
          throw (coverageFailure pointPath "next-use-statement" ordered resident)
        let statementLayout ←
          stmtFuel fuel pointPath ctx pinned ordered source facts
        if StackSchedule.alwaysExits source then
          pure statementLayout
        else
          let afterDemand := StackSchedule.required pinned
            (StackSchedule.nextLive facts.liveAfter rest restFacts)
          if !StackSchedule.covers statementLayout afterDemand then
            throw
              (coverageFailure pointPath "next-use-fallthrough"
                statementLayout afterDemand)
          let retained ←
            match Transition.build? statementLayout afterDemand with
            | some transition => pure transition
            | none =>
                throw
                  (transitionFailure pointPath "next-use-fallthrough"
                    statementLayout afterDemand)
          listFuel fuel path ctx pinned retained.target
            rest restFacts (index + 1)
    | _, _, index =>
        .error
          { path := path ++ "/stmt[" ++ toString index ++ "]"
            phase := "next-use-shape"
            reason := "source statements and liveness points differ" }

  def stmtFuel (fuel : Nat) (path : String) (ctx : StackLowering.Ctx)
      (pinned : LiveSet) (layout : Locals.Layout) (source : Stmt)
      (facts : AllocationLivenessFacts.Point) : Except Failure Locals.Layout :=
    match fuel with
    | 0 =>
        .error { path, phase := "next-use", reason := "statement fuel exhausted" }
    | fuel + 1 =>
        match source with
        | .let_ name value => do
            if (StackAccess.Expr.check? layout 0 value).isNone then
              let access :=
                match StackAccess.Expr.firstFailure? layout 0 value with
                | none => "unknown"
                | some (failed, offset, depth) =>
                    failed ++ "@offset=" ++ toString offset ++
                      ",depth=" ++ toString depth
              throw
                { path, phase := "next-use-access"
                  reason :=
                    "declaration expression remains inaccessible; layout=" ++
                      reprStr layout ++ "; priority=" ++
                      reprStr (statementPriority ctx source) ++
                      "; first=" ++ access }
            if name ∈ layout then
              throw { path, phase := "next-use-layout", reason := "duplicate binding" }
            pure (name :: layout)
        | .block body | .if_ _ body => do
            if (directAccess? ctx layout source).isNone then
              throw
                { path, phase := "next-use-access"
                  reason := stmtKind source ++ " remains inaccessible" }
            let childFacts ←
              match facts.regions with
              | [child] => pure child
              | _ =>
                  throw
                    { path, phase := "next-use-shape"
                      reason := "expected one child region" }
            let childFinal ←
              blockFuel fuel (path ++ "/region[0]") ctx
                (StackSchedule.layoutSet layout) layout body childFacts
            restore path childFinal layout
        | .switch scrutinee cases defaultBody => do
            if (StackAccess.Expr.check? layout 0 scrutinee).isNone then
              throw
                { path, phase := "next-use-access"
                  reason := "switch scrutinee remains inaccessible" }
            let caseFacts := facts.regions.take cases.length
            let defaultFacts := facts.regions.drop cases.length
            casesFuel fuel path ctx layout cases caseFacts 0
            defaultFuel fuel path ctx layout defaultBody defaultFacts
            pure layout
        | .for_ init condition post body => do
            let regions ←
              match facts.regions with
              | [initFacts, postFacts, bodyFacts] =>
                  pure (initFacts, postFacts, bodyFacts)
              | _ =>
                  throw
                    { path, phase := "next-use-shape"
                      reason := "expected init, post, and body regions" }
            let initFinal ←
              blockFuel fuel (path ++ "/loop-init") ctx
                (StackSchedule.layoutSet layout) layout init regions.1
            if (StackAccess.Expr.check? initFinal 0 condition).isNone then
              throw
                { path, phase := "next-use-access"
                  reason := "loop condition remains inaccessible" }
            let loopPinned := StackSchedule.layoutSet initFinal
            let postFinal ←
              blockFuel fuel (path ++ "/loop-post") ctx loopPinned
                initFinal post regions.2.1
            let _ ← restore (path ++ "/loop-post") postFinal initFinal
            let bodyFinal ←
              blockFuel fuel (path ++ "/loop-body") ctx loopPinned
                initFinal body regions.2.2
            let _ ← restore (path ++ "/loop-body") bodyFinal initFinal
            pure layout
        | _ =>
            if (directAccess? ctx layout source).isSome then pure layout
            else
              .error
                { path, phase := "next-use-access"
                  reason := stmtKind source ++ " remains inaccessible" }

  def casesFuel (fuel : Nat) (path : String) (ctx : StackLowering.Ctx)
      (layout : Locals.Layout) :
      List (Word × Block) → List AllocationLivenessFacts.Region → Nat →
        Except Failure Unit
    | (_, body) :: rest, facts :: restFacts, index => do
        let final ←
          blockFuel fuel (path ++ "/case[" ++ toString index ++ "]") ctx
            (StackSchedule.layoutSet layout) layout body facts
        let _ ← restore (path ++ "/case[" ++ toString index ++ "]") final layout
        casesFuel fuel path ctx layout rest restFacts (index + 1)
    | [], [], _ => pure ()
    | _, _, _ =>
        throw
          { path, phase := "next-use-shape"
            reason := "switch cases and facts differ" }

  def defaultFuel (fuel : Nat) (path : String) (ctx : StackLowering.Ctx)
      (layout : Locals.Layout) :
      Option Block → List AllocationLivenessFacts.Region → Except Failure Unit
    | some body, [facts] => do
        let final ←
          blockFuel fuel (path ++ "/default") ctx
            (StackSchedule.layoutSet layout) layout body facts
        let _ ← restore (path ++ "/default") final layout
        pure ()
    | none, [] => pure ()
    | _, _ =>
        throw
          { path, phase := "next-use-shape"
            reason := "switch default and facts differ" }
end

def block (path : String) (ctx : StackLowering.Ctx)
    (demand : Demand) (pinned : LiveSet) (layout : Locals.Layout)
    (source : Block) : Except Failure Locals.Layout := do
  let facts ←
    match AllocationLivenessFacts.annotateBlock? demand source with
    | some facts => pure facts
    | none =>
        throw { path, phase := "next-use-liveness", reason := "analysis failed" }
  blockFuel (AllocationLiveness.analysisFuel source) path ctx
    pinned layout source facts

end NextUse

structure UnitReport where
  name : String
  metrics : Metrics := {}
  livenessOk : Bool := false
  scheduleOk : Bool := false
  accessFailures : Nat := 0
  loweringOk : Bool := false
  firstFailure? : Option Failure := none
  nextUseOk : Bool := false
  nextUseFailure? : Option Failure := none
  discardMetrics : DiscardMetrics := {}
  deriving Repr

def functionReport (functions : List FunDef) (fn : FunDef) : UnitReport :=
  let path := "function:" ++ fn.name
  let demand := StackLowering.functionDemand fn
  let layout := StackLowering.functionBodyLayout fn
  let ctx : StackLowering.Ctx := { functions, returns := fn.returns }
  let nextUse :=
    NextUse.block path ctx demand ∅ layout fn.body
  match AllocationLivenessFacts.annotateBlock? demand fn.body with
  | none =>
      { name := path
        nextUseOk := nextUse.isOk
        nextUseFailure? :=
          match nextUse with | .error failure => some failure | _ => none
        firstFailure? :=
          some { path, phase := "liveness", reason := "analysis returned none" } }
  | some facts =>
      let metrics := Metrics.block fn.body facts
      match StackSchedule.scheduleBlock? ∅ layout fn.body facts with
      | none =>
          { name := path, metrics, livenessOk := true
            nextUseOk := nextUse.isOk
            nextUseFailure? := match nextUse with | .error failure => some failure | _ => none
            firstFailure? := firstScheduleFailure? path ∅ layout fn.body facts }
      | some schedule =>
          let accessFailures := accessFailuresBlock ctx fn.body schedule
          let loweringOk := (StackLowering.lowerFunction? functions fn).isSome
          { name := path, metrics, livenessOk := true, scheduleOk := true
            accessFailures, loweringOk
            discardMetrics :=
              DiscardMetrics.regionFuel
                (AllocationLiveness.analysisFuel fn.body) schedule
            nextUseOk := nextUse.isOk
            nextUseFailure? := match nextUse with | .error failure => some failure | _ => none
            firstFailure? :=
              if loweringOk then none
              else if accessFailures = 0 then
                some
                  { path, phase := "lowering"
                    reason := "final return accessibility or lowering shape failed" }
              else
                firstAccessFailure? path ctx fn.body schedule }

def bodyReport (program : Program) : UnitReport :=
  let path := "program-body"
  let demand : Demand := { normal := ∅ }
  let ctx : StackLowering.Ctx := { functions := program.functions, returns := [] }
  let nextUse := NextUse.block path ctx demand ∅ [] program.body
  match AllocationLivenessFacts.annotateBlock? demand program.body with
  | none =>
      { name := path
        nextUseOk := nextUse.isOk
        nextUseFailure? := match nextUse with | .error failure => some failure | _ => none
        firstFailure? :=
          some { path, phase := "liveness", reason := "analysis returned none" } }
  | some facts =>
      let metrics := Metrics.block program.body facts
      match StackSchedule.scheduleBlock? ∅ [] program.body facts with
      | none =>
          { name := path, metrics, livenessOk := true
            nextUseOk := nextUse.isOk
            nextUseFailure? := match nextUse with | .error failure => some failure | _ => none
            firstFailure? := firstScheduleFailure? path ∅ [] program.body facts }
      | some schedule =>
          let accessFailures := accessFailuresBlock ctx program.body schedule
          let loweringOk :=
            (StackLowering.lowerBlock? ctx demand ∅ [] program.body).isSome
          { name := path, metrics, livenessOk := true, scheduleOk := true
            accessFailures, loweringOk
            discardMetrics :=
              DiscardMetrics.regionFuel
                (AllocationLiveness.analysisFuel program.body) schedule
            nextUseOk := nextUse.isOk
            nextUseFailure? := match nextUse with | .error failure => some failure | _ => none
            firstFailure? :=
              if loweringOk then none
              else if accessFailures = 0 then
                some
                  { path, phase := "lowering"
                    reason := "lowering shape failed" }
              else
                firstAccessFailure? path ctx program.body schedule }

def programReports (program : Program) : List UnitReport :=
  program.functions.map (functionReport program.functions) ++
    [bodyReport program]

structure Summary where
  units : Nat := 0
  livenessOk : Nat := 0
  scheduleOk : Nat := 0
  loweringOk : Nat := 0
  nextUseOk : Nat := 0
  accessFailures : Nat := 0
  metrics : Metrics := {}
  discardMetrics : DiscardMetrics := {}
  deriving Repr

def Summary.add (summary : Summary) (report : UnitReport) : Summary :=
  { units := summary.units + 1
    livenessOk := summary.livenessOk + if report.livenessOk then 1 else 0
    scheduleOk := summary.scheduleOk + if report.scheduleOk then 1 else 0
    loweringOk := summary.loweringOk + if report.loweringOk then 1 else 0
    nextUseOk := summary.nextUseOk + if report.nextUseOk then 1 else 0
    accessFailures := summary.accessFailures + report.accessFailures
    metrics := Metrics.combine summary.metrics report.metrics
    discardMetrics :=
      DiscardMetrics.combine summary.discardMetrics report.discardMetrics }

def summarize (reports : List UnitReport) : Summary :=
  reports.foldl Summary.add {}

def firstFailure? : List UnitReport → Option (String × Failure)
  | [] => none
  | report :: rest =>
      match report.firstFailure? with
      | some failure => some (report.name, failure)
      | none => firstFailure? rest

end StackDiagnostics
end Functions
end EvmCompiler
