import EvmCompiler.Functions.LoweringCore
import EvmCompiler.Functions.StackSchedule

/-!
Stack-only lowering driven by compiler-owned liveness and layout artifacts.

The public entry points compute their own liveness facts and schedules.  The
private recursive lowering consumes those artifacts only to insert ordinary
Locals shuffle/cleanup statements around the unchanged structured source.
-/

namespace EvmCompiler
namespace Functions
namespace StackLowering

open AllocationLiveness
open AllocationLivenessFacts
open AllocationLayout
open StackSchedule

structure Ctx where
  functions : List FunDef
  returns : List Name

def transitionStmts (transition : Transition) : List Locals.Stmt :=
  transition.schedule.statements

def returnWord (name : Name) : Expr 1 :=
  .prim .add
    (by
      simpa using
        Locals.ExprSeq.cons (.var name)
          (Locals.ExprSeq.cons (.lit Lower.zero) Locals.ExprSeq.nil))

def returnWords : (names : List Name) → Locals.ExprSeq names.length
  | [] => .nil
  | name :: rest =>
      by
        simpa [Nat.add_comm] using
          (Locals.ExprSeq.cons (left := 1) (right := rest.length)
            (returnWord name) (returnWords rest))

def pushWordReturns : List Name → List Locals.Stmt
  | [] => []
  | name :: rest => [.exprs (returnWords (name :: rest))]

def callStmts? (ctx : Ctx) (targets : List Name)
    (functionName : Name) (args : List (Expr 1)) :
    Option (List Locals.Stmt) := do
  let fn ← FunList.find? functionName ctx.functions
  if args.length = fn.params.length then pure () else none
  if targets.length = fn.returns.length then pure () else none
  if targets.Nodup then pure () else none
  some
    ([.exprs (Lower.argExprs args), .call functionName] ++
      Lower.assignReturnedTops targets)

mutual
  def lowerBlockFuel (fuel : Nat) (ctx : Ctx)
      (source : Block) (schedule : StackSchedule.Region) :
      Option Locals.Block :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
        let body ←
          lowerStmtListFuel fuel ctx source.stmts schedule.points
        some
          { stmts :=
              transitionStmts schedule.entry ++ body }

  def lowerStmtListFuel (fuel : Nat) (ctx : Ctx) :
      List Stmt → List StackSchedule.Point →
        Option (List Locals.Stmt)
    | [], [] => some []
    | stmt :: rest, point :: points => do
        let head ← lowerPointFuel fuel ctx stmt point
        if point.fallsThrough then
          let tail ← lowerStmtListFuel fuel ctx rest points
          some (head ++ tail)
        else
          some head
    | _, _ => none

  def lowerCasesFuel (fuel : Nat) (ctx : Ctx) :
      List (Word × Block) → List StackSchedule.Region →
        Option (List (Word × Locals.Block))
    | [], [] => some []
    | (value, body) :: rest, region :: regions => do
        let loweredBody ← lowerBlockFuel fuel ctx body region
        let loweredRest ← lowerCasesFuel fuel ctx rest regions
        some ((value, loweredBody) :: loweredRest)
    | _, _ => none

  def lowerDefaultFuel (fuel : Nat) (ctx : Ctx) :
      Option Block → List StackSchedule.Region →
        Option (Option Locals.Block)
    | none, [] => some none
    | some body, [region] => do
        let lowered ← lowerBlockFuel fuel ctx body region
        some (some lowered)
    | _, _ => none

  def lowerPointFuel (fuel : Nat) (ctx : Ctx)
      (source : Stmt) (point : StackSchedule.Point) :
      Option (List Locals.Stmt) :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
        if point.fallsThrough = !StackSchedule.alwaysExits source then
          pure ()
        else
          none
        let core ←
          match source, point.regions with
          | .expr expr, [] => some [.expr expr]
          | .let_ name value, [] => some [.let_ name value]
          | .assign name value, [] => some [.assign name value]
          | .block body, [region] => do
              let lowered ← lowerBlockFuel fuel ctx body region
              some [.block lowered]
          | .if_ cond body, [region] => do
              let lowered ← lowerBlockFuel fuel ctx body region
              some [.if_ cond lowered]
          | .switch scrutinee cases defaultBody, regions => do
              let caseCount := cases.length
              let caseRegions := regions.take caseCount
              let defaultRegions := regions.drop caseCount
              let loweredCases ←
                lowerCasesFuel fuel ctx cases caseRegions
              let loweredDefault ←
                lowerDefaultFuel fuel ctx defaultBody defaultRegions
              some [.switch scrutinee loweredCases loweredDefault]
          | .for_ init cond post body,
              [initRegion, postRegion, bodyRegion] => do
              let loweredInit ← lowerBlockFuel fuel ctx init initRegion
              let loweredPost ← lowerBlockFuel fuel ctx post postRegion
              let loweredBody ← lowerBlockFuel fuel ctx body bodyRegion
              some [.for_ loweredInit cond loweredPost loweredBody]
          | .brk, [] => some [.brk]
          | .cont, [] => some [.cont]
          | .leave, [] =>
              some (pushWordReturns ctx.returns ++ [.leave])
          | .call targets functionName args, [] =>
              callStmts? ctx targets functionName args
          | .terminal kind, [] => some [.terminal kind]
          | .terminalArgs kind args, [] =>
              some [.terminalArgs kind args]
          | _, _ => none
        if point.fallsThrough then
          match point.retain? with
          | some retain => some (core ++ transitionStmts retain)
          | none => none
        else if point.retain?.isNone then
          some core
        else
          none
end

def lowerScheduledBlock? (ctx : Ctx) (source : Block)
    (schedule : StackSchedule.Region) : Option Locals.Block :=
  lowerBlockFuel (AllocationLiveness.analysisFuel source)
    ctx source schedule

def lowerBlock? (ctx : Ctx) (demand : Demand)
    (pinned : LiveSet) (layout : Locals.Layout)
    (source : Block) : Option Locals.Block := do
  let facts ← AllocationLivenessFacts.annotateBlock? demand source
  let schedule ← StackSchedule.scheduleBlock? pinned layout source facts
  lowerScheduledBlock? ctx source schedule

theorem lowerBlock?_components
    {ctx : Ctx} {demand : Demand} {pinned : LiveSet}
    {layout : Locals.Layout} {source : Block} {lowered : Locals.Block}
    (hLower : lowerBlock? ctx demand pinned layout source = some lowered) :
    ∃ facts schedule,
      AllocationLivenessFacts.annotateBlock? demand source = some facts ∧
      StackSchedule.scheduleBlock? pinned layout source facts =
        some schedule ∧
      lowerScheduledBlock? ctx source schedule = some lowered := by
  unfold lowerBlock? at hLower
  obtain ⟨facts, hFacts, hAfterFacts⟩ :=
    Option.bind_eq_some_iff.mp hLower
  obtain ⟨schedule, hSchedule, hLowered⟩ :=
    Option.bind_eq_some_iff.mp hAfterFacts
  exact ⟨facts, schedule, hFacts, hSchedule, hLowered⟩

def functionDemand (fn : FunDef) : Demand :=
  let returns := fn.returns.toFinset
  { normal := returns, leave := returns }

def functionBodyLayout (fn : FunDef) : Locals.Layout :=
  fn.returns.reverse ++ fn.params.reverse

def lowerFunction? (functions : List FunDef) (fn : FunDef) :
    Option Locals.Proc := do
  let entryLayout := fn.params.reverse
  let bodyLayout := functionBodyLayout fn
  let body ←
    lowerBlock?
      { functions, returns := fn.returns }
      (functionDemand fn) ∅ bodyLayout fn.body
  some
    { name := fn.name
      argc := fn.params.length
      retc := fn.returns.length
      entryLayout
      body :=
        { stmts :=
            [Lower.bindEntryLayout entryLayout] ++
              Lower.initReturns fn.returns ++
              body.stmts ++
              pushWordReturns fn.returns } }

def lowerFunctions? (allFunctions : List FunDef) :
    List FunDef → Option (List Locals.Proc)
  | [] => some []
  | fn :: rest => do
      let proc ← lowerFunction? allFunctions fn
      let tail ← lowerFunctions? allFunctions rest
      some (proc :: tail)

def lowerProgram? (program : Program) : Option Locals.Program := do
  let procs ← lowerFunctions? program.functions program.functions
  let body ←
    lowerBlock?
      { functions := program.functions, returns := [] }
      { normal := ∅ } ∅ [] program.body
  some { procs, body }

namespace Examples

def word (value : Nat) : Word :=
  EvmYul.UInt256.ofNat value

def add (left right : Expr 1) : Expr 1 :=
  .prim .add
    (by
      simpa using
        Locals.ExprSeq.cons left
          (Locals.ExprSeq.cons right Locals.ExprSeq.nil))

def deadProgram : Program :=
  { functions := []
    body := StackSchedule.Examples.sequentialDeadSource }

theorem deadProgram_lowers : (lowerProgram? deadProgram).isSome = true := by
  native_decide

def identity : FunDef :=
  { name := "identity"
    params := ["input"]
    returns := ["output"]
    body :=
      { stmts :=
          [.assign "output" (.var "input")] } }

def dormantCallProgram : Program :=
  { functions := [identity]
    body :=
      { stmts :=
          [.let_ "callerLive" (.lit (word 7)),
           .let_ "result" (.lit (word 0)),
           .call ["result"] "identity" [.lit (word 3)],
           .let_ "sum" (add (.var "result") (.var "callerLive")),
           .terminal .stop] } }

theorem dormantCallProgram_lowers :
    (lowerProgram? dormantCallProgram).isSome = true := by
  native_decide

def controlProgram : Program :=
  { functions := []
    body :=
      { stmts :=
          [.let_ "value" (.lit (word 1)),
           .if_ (.lit (word 1))
             { stmts := [.assign "value" (.lit (word 2))] },
           .switch (.var "value")
             [(word 0,
                { stmts := [.assign "value" (.lit (word 3))] })]
             (some
               { stmts := [.assign "value" (.lit (word 4))] }),
           .for_ { stmts := [] } (.lit (word 0))
             { stmts := [] } { stmts := [] },
           .terminal .stop] } }

theorem controlProgram_lowers :
    (lowerProgram? controlProgram).isSome = true := by
  native_decide

end Examples

end StackLowering
end Functions
end EvmCompiler
