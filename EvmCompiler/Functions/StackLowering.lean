import EvmCompiler.Functions.LoweringCore
import EvmCompiler.Functions.StackAccess
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

def exitStmts : Option Join → List Locals.Stmt
  | none => []
  | some exit => exit.statements

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

theorem returnWord_eval
    {name : Name} {state : Locals.Source.State} {value : Word}
    (hValue : state.vars name = some value) :
    Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
        (returnWord name) state = .ok (state, [value]) := by
  cases value with
  | mk val =>
      simp [returnWord, Locals.Source.Expr.eval,
        Locals.Source.Expr.ExprSeq.eval,
        Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Expressions.Structured.BasicOp.inputs,
        Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push,
        hValue, Lower.zero, EvmYul.UInt256.add,
        EvmYul.UInt256.ofNat,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Locals.Source.State.withShared, Id.run]

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

def pointAccess? (ctx : Ctx) (source : Stmt)
    (point : StackSchedule.Point) : Option Unit :=
  match source, point.regions with
  | .expr expr, _ => StackAccess.Expr.check? point.beforeLayout 0 expr
  | .let_ _ value, _ =>
      StackAccess.Expr.check? point.beforeLayout 0 value
  | .assign name value, _ =>
      StackAccess.assign? point.beforeLayout name value
  | .if_ condition _, _ =>
      StackAccess.Expr.check? point.beforeLayout 0 condition
  | .switch scrutinee _ _, _ =>
      StackAccess.Expr.check? point.beforeLayout 0 scrutinee
  | .for_ _ condition _ _, initRegion :: _ =>
      StackAccess.Expr.check? initRegion.finalLayout 0 condition
  | .leave, _ =>
      StackAccess.ExprSeq.check? point.beforeLayout 0
        (returnWords ctx.returns)
  | .call targets _ args, _ =>
      StackAccess.call? point.beforeLayout targets args
  | .terminalArgs _ args, _ =>
      StackAccess.ExprSeq.check? point.beforeLayout 0 args
  | _, _ => some ()

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
              transitionStmts schedule.entry ++ body ++
                exitStmts schedule.exit? }

  def lowerStmtListFuel (fuel : Nat) (ctx : Ctx) :
      List Stmt → List StackSchedule.Point →
        Option (List Locals.Stmt)
    | [], [] => some []
    | stmt :: rest, point :: points => do
        let order ← point.order?
        let head ← lowerPointFuel fuel ctx stmt point
        if point.fallsThrough then
          let tail ← lowerStmtListFuel fuel ctx rest points
          some (order.statements ++ head ++ tail)
        else
          some (order.statements ++ head)
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
        let _ ← pointAccess? ctx source point
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
          | .brk, [] =>
              some (exitStmts point.exit? ++ [.brk])
          | .cont, [] =>
              some (exitStmts point.exit? ++ [.cont])
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

theorem lowerBlockFuel_components
    {fuel : Nat} {ctx : Ctx} {source : Block}
    {schedule : StackSchedule.Region} {lowered : Locals.Block}
    (hLower : lowerBlockFuel fuel ctx source schedule = some lowered) :
    ∃ body,
      lowerStmtListFuel (fuel - 1) ctx source.stmts schedule.points =
          some body ∧
        lowered.stmts =
          transitionStmts schedule.entry ++ body ++
            exitStmts schedule.exit? := by
  cases fuel with
  | zero => simp [lowerBlockFuel] at hLower
  | succ fuel =>
      simp only [lowerBlockFuel] at hLower
      obtain ⟨body, hBody, hResult⟩ :=
        Option.bind_eq_some_iff.mp hLower
      have hLowered := Option.some.inj hResult
      exact
        ⟨body, by simpa using hBody,
          by
            simpa using
              congrArg Locals.Block.stmts hLowered.symm⟩

theorem lowerStmtListFuel_cons_components
    {fuel : Nat} {ctx : Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (stmt :: rest) (point :: points) =
        some lowered) :
    ∃ order head,
      point.order? = some order ∧
        lowerPointFuel fuel ctx stmt point = some head ∧
        ((point.fallsThrough = true ∧
            ∃ tail,
              lowerStmtListFuel fuel ctx rest points = some tail ∧
              lowered = order.statements ++ head ++ tail) ∨
          (point.fallsThrough = false ∧
            lowered = order.statements ++ head)) := by
  simp only [lowerStmtListFuel] at hLower
  obtain ⟨order, hOrder, hAfterOrder⟩ :=
    Option.bind_eq_some_iff.mp hLower
  obtain ⟨head, hHead, hAfterHead⟩ :=
    Option.bind_eq_some_iff.mp hAfterOrder
  refine ⟨order, head, hOrder, hHead, ?_⟩
  cases hFalls : point.fallsThrough with
  | false =>
      rw [hFalls] at hAfterHead
      exact .inr ⟨rfl, (Option.some.inj hAfterHead).symm⟩
  | true =>
      rw [hFalls] at hAfterHead
      obtain ⟨tail, hTail, hResult⟩ :=
        Option.bind_eq_some_iff.mp hAfterHead
      exact .inl ⟨rfl, tail, hTail, (Option.some.inj hResult).symm⟩

theorem lowerStmtListFuel_cons_fallsThrough_components
    {fuel : Nat} {ctx : Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (stmt :: rest) (point :: points) =
        some lowered)
    (hFalls : point.fallsThrough = true) :
    ∃ order head tail,
      point.order? = some order ∧
        lowerPointFuel fuel ctx stmt point = some head ∧
        lowerStmtListFuel fuel ctx rest points = some tail ∧
        lowered = order.statements ++ head ++ tail := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  have hRegular := hCases.resolve_right (by
    intro hAbrupt
    rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1)
  obtain ⟨_hFalls, tail, hTail, hLowered⟩ := hRegular
  exact ⟨order, head, tail, hOrder, hHead, hTail, hLowered⟩

theorem lowerStmtListFuel_cons_nonfallthrough_components
    {fuel : Nat} {ctx : Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (stmt :: rest) (point :: points) =
        some lowered)
    (hFalls : point.fallsThrough = false) :
    ∃ order head,
      point.order? = some order ∧
        lowerPointFuel fuel ctx stmt point = some head ∧
        lowered = order.statements ++ head := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hRegular.1] at hFalls
    exact Bool.noConfusion hFalls)
  exact ⟨order, head, hOrder, hHead, hAbrupt.2⟩

theorem lowerStmtListFuel_nil_components
    {fuel : Nat} {ctx : Ctx} {lowered : List Locals.Stmt}
    (hLower : lowerStmtListFuel fuel ctx [] [] = some lowered) :
    lowered = [] := by
  simpa [lowerStmtListFuel] using hLower

theorem lowerPointFuel_expr_components
    {fuel : Nat} {ctx : Ctx} {expr : Expr 0}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower : lowerPointFuel fuel ctx (.expr expr) point = some lowered) :
    ∃ retain,
      pointAccess? ctx (.expr expr) point = some () ∧
      point.fallsThrough = true ∧ point.regions = [] ∧
      point.retain? = some retain ∧
      lowered = [.expr expr] ++ transitionStmts retain := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.expr expr) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough =
                !StackSchedule.alwaysExits (.expr expr)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsTrue : point.fallsThrough = true := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsTrue] at hLower
                cases hRetain : point.retain? with
                | none => simp [hRetain] at hLower
                | some retain =>
                    rw [hRetain] at hLower
                    exact
                      ⟨retain, rfl, hFallsTrue, rfl, rfl,
                        by simpa using hLower.symm⟩
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_let_components
    {fuel : Nat} {ctx : Ctx} {name : Name} {value : Expr 1}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower : lowerPointFuel fuel ctx (.let_ name value) point = some lowered) :
    ∃ retain,
      pointAccess? ctx (.let_ name value) point = some () ∧
      point.fallsThrough = true ∧ point.regions = [] ∧
      point.retain? = some retain ∧
      lowered = [.let_ name value] ++ transitionStmts retain := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.let_ name value) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough =
                !StackSchedule.alwaysExits (.let_ name value)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsTrue : point.fallsThrough = true := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsTrue] at hLower
                cases hRetain : point.retain? with
                | none => simp [hRetain] at hLower
                | some retain =>
                    rw [hRetain] at hLower
                    exact
                      ⟨retain, rfl, hFallsTrue, rfl, rfl,
                        by simpa using hLower.symm⟩
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_assign_components
    {fuel : Nat} {ctx : Ctx} {name : Name} {value : Expr 1}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerPointFuel fuel ctx (.assign name value) point = some lowered) :
    ∃ retain,
      pointAccess? ctx (.assign name value) point = some () ∧
      point.fallsThrough = true ∧ point.regions = [] ∧
      point.retain? = some retain ∧
      lowered = [.assign name value] ++ transitionStmts retain := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.assign name value) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough =
                !StackSchedule.alwaysExits (.assign name value)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsTrue : point.fallsThrough = true := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsTrue] at hLower
                cases hRetain : point.retain? with
                | none => simp [hRetain] at hLower
                | some retain =>
                    rw [hRetain] at hLower
                    exact
                      ⟨retain, rfl, hFallsTrue, rfl, rfl,
                        by simpa using hLower.symm⟩
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_terminal_components
    {fuel : Nat} {ctx : Ctx} {kind : Assembly.HaltKind}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerPointFuel fuel ctx (.terminal kind) point = some lowered) :
    pointAccess? ctx (.terminal kind) point = some () ∧
      point.fallsThrough = false ∧ point.regions = [] ∧
      point.retain? = none ∧ lowered = [.terminal kind] := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.terminal kind) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough =
                !StackSchedule.alwaysExits (.terminal kind)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsFalse : point.fallsThrough = false := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsFalse] at hLower
                cases hRetain : point.retain? with
                | none =>
                    rw [hRetain] at hLower
                    exact
                      ⟨rfl, hFallsFalse, rfl, rfl,
                        by simpa using hLower.symm⟩
                | some retain => simp [hRetain] at hLower
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_terminalArgs_components
    {fuel : Nat} {ctx : Ctx} {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerPointFuel fuel ctx (.terminalArgs kind args) point =
        some lowered) :
    pointAccess? ctx (.terminalArgs kind args) point = some () ∧
      point.fallsThrough = false ∧ point.regions = [] ∧
      point.retain? = none ∧
      lowered = [.terminalArgs kind args] := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.terminalArgs kind args) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough =
                !StackSchedule.alwaysExits (.terminalArgs kind args)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsFalse : point.fallsThrough = false := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsFalse] at hLower
                cases hRetain : point.retain? with
                | none =>
                    rw [hRetain] at hLower
                    exact
                      ⟨rfl, hFallsFalse, rfl, rfl,
                        by simpa using hLower.symm⟩
                | some retain => simp [hRetain] at hLower
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_switch_components
    {fuel : Nat} {ctx : Ctx} {scrutinee : Expr 1}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerPointFuel fuel ctx (.switch scrutinee cases defaultBody) point =
        some lowered) :
    ∃ loweredCases loweredDefault retain,
      pointAccess? ctx (.switch scrutinee cases defaultBody) point = some () ∧
        point.fallsThrough = true ∧
        lowerCasesFuel (fuel - 1) ctx cases
            (point.regions.take cases.length) = some loweredCases ∧
        lowerDefaultFuel (fuel - 1) ctx defaultBody
            (point.regions.drop cases.length) = some loweredDefault ∧
        point.retain? = some retain ∧
        lowered =
          [.switch scrutinee loweredCases loweredDefault] ++
            transitionStmts retain := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess :
          pointAccess? ctx (.switch scrutinee cases defaultBody) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough =
                !StackSchedule.alwaysExits
                  (.switch scrutinee cases defaultBody)
          · rw [if_pos hFalls] at hLower
            have hFallsTrue : point.fallsThrough = true := by
              simpa [StackSchedule.alwaysExits] using hFalls
            rw [hFallsTrue] at hLower
            change
              (do
                let loweredCases ←
                  lowerCasesFuel fuel ctx cases
                    (point.regions.take cases.length)
                let loweredDefault ←
                  lowerDefaultFuel fuel ctx defaultBody
                    (point.regions.drop cases.length)
                match point.retain? with
                | some retain =>
                    some
                      ([.switch scrutinee loweredCases loweredDefault] ++
                        transitionStmts retain)
                | none => none) = some lowered at hLower
            obtain ⟨loweredCases, hCases, hAfterCases⟩ :=
              Option.bind_eq_some_iff.mp hLower
            obtain ⟨loweredDefault, hDefault, hAfterDefault⟩ :=
              Option.bind_eq_some_iff.mp hAfterCases
            cases hRetain : point.retain? with
            | none => simp [hRetain] at hAfterDefault
            | some retain =>
                rw [hRetain] at hAfterDefault
                exact ⟨loweredCases, loweredDefault, retain, rfl,
                  hFallsTrue, by simpa using hCases,
                  by simpa using hDefault, rfl,
                  by simpa using hAfterDefault.symm⟩
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerCasesFuel_nil_components
    {fuel : Nat} {ctx : Ctx} {lowered : List (Word × Locals.Block)}
    (hLower : lowerCasesFuel fuel ctx [] [] = some lowered) :
    lowered = [] := by
  simpa [lowerCasesFuel] using hLower.symm

theorem lowerCasesFuel_cons_components
    {fuel : Nat} {ctx : Ctx} {value : Word} {body : Block}
    {rest : List (Word × Block)} {region : StackSchedule.Region}
    {regions : List StackSchedule.Region} {loweredBody : Locals.Block}
    {loweredRest : List (Word × Locals.Block)}
    (hLower :
      lowerCasesFuel fuel ctx ((value, body) :: rest) (region :: regions) =
        some ((value, loweredBody) :: loweredRest)) :
    lowerBlockFuel fuel ctx body region = some loweredBody ∧
      lowerCasesFuel fuel ctx rest regions = some loweredRest := by
  cases fuel with
  | zero => simp [lowerCasesFuel, lowerBlockFuel] at hLower
  | succ fuel =>
      simp only [lowerCasesFuel] at hLower
      obtain ⟨actualBody, hBody, hAfterBody⟩ :=
        Option.bind_eq_some_iff.mp hLower
      obtain ⟨actualRest, hRest, hResult⟩ :=
        Option.bind_eq_some_iff.mp hAfterBody
      have hList := Option.some.inj hResult
      injection hList with hBodyEq hRestEq
      have hActualBody : actualBody = loweredBody := congrArg Prod.snd hBodyEq
      subst actualBody
      subst actualRest
      exact ⟨hBody, hRest⟩

theorem lowerDefaultFuel_none_components
    {fuel : Nat} {ctx : Ctx} {lowered : Option Locals.Block}
    (hLower : lowerDefaultFuel fuel ctx none [] = some lowered) :
    lowered = none := by
  simpa [lowerDefaultFuel] using hLower.symm

theorem lowerDefaultFuel_some_components
    {fuel : Nat} {ctx : Ctx} {body : Block}
    {region : StackSchedule.Region} {loweredBody : Locals.Block}
    (hLower :
      lowerDefaultFuel fuel ctx (some body) [region] =
        some (some loweredBody)) :
    lowerBlockFuel fuel ctx body region = some loweredBody := by
  cases fuel with
  | zero => simp [lowerDefaultFuel, lowerBlockFuel] at hLower
  | succ fuel =>
      simp only [lowerDefaultFuel] at hLower
      obtain ⟨actualBody, hBody, hResult⟩ :=
        Option.bind_eq_some_iff.mp hLower
      have hSome := Option.some.inj hResult
      injection hSome with hBodyEq
      subst actualBody
      exact hBody

theorem lowerPointFuel_brk_components
    {fuel : Nat} {ctx : Ctx}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower : lowerPointFuel fuel ctx .brk point = some lowered) :
    pointAccess? ctx .brk point = some () ∧
      point.fallsThrough = false ∧ point.regions = [] ∧
      point.retain? = none ∧
      lowered = exitStmts point.exit? ++ [.brk] := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx .brk point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough = !StackSchedule.alwaysExits .brk
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsFalse : point.fallsThrough = false := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsFalse] at hLower
                cases hRetain : point.retain? with
                | none =>
                    rw [hRetain] at hLower
                    exact
                      ⟨rfl, hFallsFalse, rfl, rfl,
                        by simpa using hLower.symm⟩
                | some retain => simp [hRetain] at hLower
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_cont_components
    {fuel : Nat} {ctx : Ctx}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower : lowerPointFuel fuel ctx .cont point = some lowered) :
    pointAccess? ctx .cont point = some () ∧
      point.fallsThrough = false ∧ point.regions = [] ∧
      point.retain? = none ∧
      lowered = exitStmts point.exit? ++ [.cont] := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx .cont point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough = !StackSchedule.alwaysExits .cont
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil =>
                rw [hRegions] at hLower
                have hFallsFalse : point.fallsThrough = false := by
                  simpa [StackSchedule.alwaysExits] using hFalls
                rw [hFallsFalse] at hLower
                cases hRetain : point.retain? with
                | none =>
                    rw [hRetain] at hLower
                    exact
                      ⟨rfl, hFallsFalse, rfl, rfl,
                        by simpa using hLower.symm⟩
                | some retain => simp [hRetain] at hLower
            | cons region regions => simp [hRegions] at hLower
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_block_components
    {fuel : Nat} {ctx : Ctx} {body : Block}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower : lowerPointFuel fuel ctx (.block body) point = some lowered) :
    ∃ region loweredBody retain,
      pointAccess? ctx (.block body) point = some () ∧
        point.fallsThrough = true ∧ point.regions = [region] ∧
        lowerBlockFuel (fuel - 1) ctx body region = some loweredBody ∧
        point.retain? = some retain ∧
        lowered = [.block loweredBody] ++ transitionStmts retain := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.block body) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough = !StackSchedule.alwaysExits (.block body)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil => simp [hRegions] at hLower
            | cons region rest =>
                cases rest with
                | cons next tail => simp [hRegions] at hLower
                | nil =>
                    cases hBody : lowerBlockFuel fuel ctx body region with
                    | none => simp [hRegions, hBody] at hLower
                    | some loweredBody =>
                        have hFallsTrue : point.fallsThrough = true := by
                          simpa [StackSchedule.alwaysExits] using hFalls
                        simp [hRegions, hBody, hFallsTrue] at hLower
                        cases hRetain : point.retain? with
                        | none => simp [hRetain] at hLower
                        | some retain =>
                            rw [hRetain] at hLower
                            exact
                              ⟨region, loweredBody, retain, rfl, hFallsTrue,
                                rfl, by simpa using hBody, rfl,
                                by simpa using hLower.symm⟩
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerPointFuel_if_components
    {fuel : Nat} {ctx : Ctx} {cond : Expr 1} {body : Block}
    {point : StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower : lowerPointFuel fuel ctx (.if_ cond body) point = some lowered) :
    ∃ region loweredBody retain,
      pointAccess? ctx (.if_ cond body) point = some () ∧
        point.fallsThrough = true ∧ point.regions = [region] ∧
        lowerBlockFuel (fuel - 1) ctx body region = some loweredBody ∧
        point.retain? = some retain ∧
        lowered = [.if_ cond loweredBody] ++ transitionStmts retain := by
  cases fuel with
  | zero => simp [lowerPointFuel] at hLower
  | succ fuel =>
      simp only [lowerPointFuel] at hLower
      cases hAccess : pointAccess? ctx (.if_ cond body) point with
      | none => simp [hAccess] at hLower
      | some unit =>
          cases unit
          rw [hAccess] at hLower
          by_cases hFalls :
              point.fallsThrough = !StackSchedule.alwaysExits (.if_ cond body)
          · rw [if_pos hFalls] at hLower
            cases hRegions : point.regions with
            | nil => simp [hRegions] at hLower
            | cons region rest =>
                cases rest with
                | cons next tail => simp [hRegions] at hLower
                | nil =>
                    cases hBody : lowerBlockFuel fuel ctx body region with
                    | none => simp [hRegions, hBody] at hLower
                    | some loweredBody =>
                        have hFallsTrue : point.fallsThrough = true := by
                          simpa [StackSchedule.alwaysExits] using hFalls
                        simp [hRegions, hBody, hFallsTrue] at hLower
                        cases hRetain : point.retain? with
                        | none => simp [hRetain] at hLower
                        | some retain =>
                            rw [hRetain] at hLower
                            exact
                              ⟨region, loweredBody, retain, rfl, hFallsTrue,
                                rfl, by simpa using hBody, rfl,
                                by simpa using hLower.symm⟩
          · rw [if_neg hFalls] at hLower
            contradiction

theorem lowerStmtListFuel_brk_components
    {fuel : Nat} {ctx : Ctx} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.brk :: rest) (point :: points) =
        some lowered) :
    ∃ order,
      point.order? = some order ∧
        pointAccess? ctx .brk point = some () ∧
        point.fallsThrough = false ∧ point.regions = [] ∧
        point.retain? = none ∧
        lowered = order.statements ++ exitStmts point.exit? ++ [.brk] := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨hAccess, hFalls, hRegions, hRetain, hHeadCode⟩ :=
    lowerPointFuel_brk_components hHead
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1)
  exact
    ⟨order, hOrder, hAccess, hFalls, hRegions, hRetain,
      by rw [hAbrupt.2, hHeadCode, List.append_assoc]⟩

theorem lowerStmtListFuel_cont_components
    {fuel : Nat} {ctx : Ctx} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.cont :: rest) (point :: points) =
        some lowered) :
    ∃ order,
      point.order? = some order ∧
        pointAccess? ctx .cont point = some () ∧
        point.fallsThrough = false ∧ point.regions = [] ∧
        point.retain? = none ∧
        lowered = order.statements ++ exitStmts point.exit? ++ [.cont] := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨hAccess, hFalls, hRegions, hRetain, hHeadCode⟩ :=
    lowerPointFuel_cont_components hHead
  have hAbrupt := hCases.resolve_left (by
    intro hRegular
    rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1)
  exact
    ⟨order, hOrder, hAccess, hFalls, hRegions, hRetain,
      by rw [hAbrupt.2, hHeadCode, List.append_assoc]⟩

theorem lowerStmtListFuel_expr_components
    {fuel : Nat} {ctx : Ctx} {expr : Expr 0} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.expr expr :: rest) (point :: points) =
        some lowered) :
    ∃ order retain tail,
      point.order? = some order ∧
        pointAccess? ctx (.expr expr) point = some () ∧
        point.retain? = some retain ∧
        lowerStmtListFuel fuel ctx rest points = some tail ∧
        lowered =
          (order.statements ++ [.expr expr] ++ transitionStmts retain) ++
            tail := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨retain, hAccess, hFalls, _hRegions, hRetain, hHeadEq⟩ :=
    lowerPointFuel_expr_components hHead
  rcases hCases with hRegular | hAbrupt
  · obtain ⟨_hFalls, tail, hTail, hLowered⟩ := hRegular
    exact
      ⟨order, retain, tail, hOrder, hAccess, hRetain, hTail,
        by simpa [hHeadEq] using hLowered⟩
  · rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1

theorem lowerStmtListFuel_let_components
    {fuel : Nat} {ctx : Ctx} {name : Name} {value : Expr 1}
    {rest : List Stmt} {point : StackSchedule.Point}
    {points : List StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.let_ name value :: rest)
          (point :: points) = some lowered) :
    ∃ order retain tail,
      point.order? = some order ∧
        pointAccess? ctx (.let_ name value) point = some () ∧
        point.retain? = some retain ∧
        lowerStmtListFuel fuel ctx rest points = some tail ∧
        lowered =
          (order.statements ++ [.let_ name value] ++
            transitionStmts retain) ++ tail := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨retain, hAccess, hFalls, _hRegions, hRetain, hHeadEq⟩ :=
    lowerPointFuel_let_components hHead
  rcases hCases with hRegular | hAbrupt
  · obtain ⟨_hFalls, tail, hTail, hLowered⟩ := hRegular
    exact
      ⟨order, retain, tail, hOrder, hAccess, hRetain, hTail,
        by simpa [hHeadEq] using hLowered⟩
  · rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1

theorem lowerStmtListFuel_assign_components
    {fuel : Nat} {ctx : Ctx} {name : Name} {value : Expr 1}
    {rest : List Stmt} {point : StackSchedule.Point}
    {points : List StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.assign name value :: rest)
          (point :: points) = some lowered) :
    ∃ order retain tail,
      point.order? = some order ∧
        pointAccess? ctx (.assign name value) point = some () ∧
        point.retain? = some retain ∧
        lowerStmtListFuel fuel ctx rest points = some tail ∧
        lowered =
          (order.statements ++ [.assign name value] ++
            transitionStmts retain) ++ tail := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨retain, hAccess, hFalls, _hRegions, hRetain, hHeadEq⟩ :=
    lowerPointFuel_assign_components hHead
  rcases hCases with hRegular | hAbrupt
  · obtain ⟨_hFalls, tail, hTail, hLowered⟩ := hRegular
    exact
      ⟨order, retain, tail, hOrder, hAccess, hRetain, hTail,
        by simpa [hHeadEq] using hLowered⟩
  · rw [hFalls] at hAbrupt
    exact Bool.noConfusion hAbrupt.1

theorem lowerStmtListFuel_terminal_components
    {fuel : Nat} {ctx : Ctx} {kind : Assembly.HaltKind}
    {rest : List Stmt} {point : StackSchedule.Point}
    {points : List StackSchedule.Point} {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.terminal kind :: rest)
          (point :: points) = some lowered) :
    ∃ order,
      point.order? = some order ∧
      pointAccess? ctx (.terminal kind) point = some () ∧
      point.retain? = none ∧
      lowered = order.statements ++ [.terminal kind] := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨hAccess, hFalls, _hRegions, hRetain, hHeadEq⟩ :=
    lowerPointFuel_terminal_components hHead
  rcases hCases with hRegular | hAbrupt
  · rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1
  · exact
      ⟨order, hOrder, hAccess, hRetain,
        by simpa [hHeadEq] using hAbrupt.2⟩

theorem lowerStmtListFuel_terminalArgs_components
    {fuel : Nat} {ctx : Ctx} {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount} {rest : List Stmt}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {lowered : List Locals.Stmt}
    (hLower :
      lowerStmtListFuel fuel ctx (.terminalArgs kind args :: rest)
          (point :: points) = some lowered) :
    ∃ order,
      point.order? = some order ∧
      pointAccess? ctx (.terminalArgs kind args) point = some () ∧
      point.retain? = none ∧
      lowered = order.statements ++ [.terminalArgs kind args] := by
  obtain ⟨order, head, hOrder, hHead, hCases⟩ :=
    lowerStmtListFuel_cons_components hLower
  obtain ⟨hAccess, hFalls, _hRegions, hRetain, hHeadEq⟩ :=
    lowerPointFuel_terminalArgs_components hHead
  rcases hCases with hRegular | hAbrupt
  · rw [hFalls] at hRegular
    exact Bool.noConfusion hRegular.1
  · exact
      ⟨order, hOrder, hAccess, hRetain,
        by simpa [hHeadEq] using hAbrupt.2⟩

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
  let ctx : Ctx := { functions, returns := fn.returns }
  let facts ←
    AllocationLivenessFacts.annotateBlock? (functionDemand fn) fn.body
  let schedule ←
    StackSchedule.scheduleBlock? ∅ bodyLayout fn.body facts
  let body ← lowerScheduledBlock? ctx fn.body schedule
  let _ ←
    StackAccess.ExprSeq.check? schedule.finalLayout 0
      (returnWords fn.returns)
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
