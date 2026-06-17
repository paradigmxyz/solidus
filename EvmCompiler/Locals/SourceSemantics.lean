import EvmCompiler.Core.Except
import EvmCompiler.Locals.Syntax
import EvmCompiler.Expressions.Syntax
import EvmCompiler.Structured.Semantics

namespace EvmCompiler
namespace Locals

/-
Stack-free source semantics for the locals abstraction.

The existing `Locals.Direct` interpreter is the checked stack-lowering backend:
it interprets locals by looking up stack depths, emitting DUP/SWAP/POP behavior,
and threading concrete EVM stacks.  This namespace is the source-side contract
the layers above locals should target instead.  Stack slots, layout depths, and
return-frame encodings belong in the compiler relation from this semantics to
the stack-shaped backend.
-/
namespace Source

abbrev Store := Name → Option Word

namespace Store

def empty : Store :=
  fun _ => none

def insert (store : Store) (name : Name) (value : Word) : Store :=
  fun key => if key = name then some value else store key

def contains (store : Store) (name : Name) : Bool :=
  (store name).isSome

def restrictTo (scope : List Name) (store : Store) : Store :=
  fun key => if key ∈ scope then store key else none

@[simp] theorem empty_apply (name : Name) :
    empty name = none := rfl

@[simp] theorem insert_self (store : Store) (name : Name) (value : Word) :
    insert store name value name = some value := by
  simp [insert]

theorem insert_of_ne {store : Store} {name other : Name} {value : Word}
    (hNe : other ≠ name) :
    insert store name value other = store other := by
  simp [insert, hNe]

theorem insert_eq_of_apply_eq
    {store : Store} {name : Name} {value : Word}
    (hValue : store name = some value) :
    insert store name value = store := by
  funext other
  by_cases hName : other = name
  · subst other
    simp [insert, hValue]
  · simp [insert, hName]

theorem restrictTo_mem {scope : List Name} {store : Store} {name : Name}
    (hMem : name ∈ scope) :
    restrictTo scope store name = store name := by
  simp [restrictTo, hMem]

theorem restrictTo_not_mem {scope : List Name} {store : Store} {name : Name}
    (hMem : name ∉ scope) :
    restrictTo scope store name = none := by
  simp [restrictTo, hMem]

theorem restrictTo_congr
    {left right : List Name} {store : Store}
    (hScope : ∀ name, name ∈ left ↔ name ∈ right) :
    restrictTo left store = restrictTo right store := by
  funext name
  by_cases hLeft : name ∈ left
  · have hRight : name ∈ right := (hScope name).mp hLeft
    simp [restrictTo, hLeft, hRight]
  · have hRight : name ∉ right := by
      intro hMem
      exact hLeft ((hScope name).mpr hMem)
    simp [restrictTo, hLeft, hRight]

end Store

structure State where
  shared : EvmYul.SharedState .EVM
  vars : Store

namespace State

def withShared (state : State) (shared : EvmYul.SharedState .EVM) :
    State :=
  { state with shared := shared }

def withVars (state : State) (vars : Store) : State :=
  { state with vars := vars }

def restrictTo (scope : List Name) (state : State) : State :=
  { state with vars := Store.restrictTo scope state.vars }

theorem restrictTo_congr
    {left right : List Name} {state : State}
    (hScope : ∀ name, name ∈ left ↔ name ∈ right) :
    state.restrictTo left = state.restrictTo right := by
  cases state
  simp [State.restrictTo, Store.restrictTo_congr hScope]

def insert (state : State) (name : Name) (value : Word) : State :=
  { state with vars := Store.insert state.vars name value }

@[simp] theorem restrictTo_shared (scope : List Name) (state : State) :
    (restrictTo scope state).shared = state.shared := rfl

@[simp] theorem insert_shared (state : State) (name : Name) (value : Word) :
    (insert state name value).shared = state.shared := rfl

theorem insert_eq_of_apply_eq
    {state : State} {name : Name} {value : Word}
    (hValue : state.vars name = some value) :
    state.insert name value = state := by
  cases state with
  | mk shared vars =>
      simp only [insert]
      rw [Store.insert_eq_of_apply_eq hValue]

end State

/--
Shared primitive semantics used by the stack-free locals interpreter.

Primitive operations may deliberately share their meaning with lower layers.
This record keeps that sharing explicit while avoiding any source-level mention
of the concrete EVM stack representation.
-/
structure PrimitiveSemantics where
  eval :
    Structured.BasicOp → EvmYul.SharedState .EVM → List Word →
      Except EVMException (EvmYul.SharedState .EVM × List Word)
  terminal :
    Assembly.HaltKind → EvmYul.SharedState .EVM → List Word →
      Except EVMException (EvmYul.SharedState .EVM)

namespace PrimitiveSemantics

/--
Continuing EVM primitives exposed at the source-primitive boundary.

Backend stack-shuffle instructions are deliberately not source primitives here:
they remain part of the lower stack-machine implementation and proofs. External
call/create and control/PC/gas-dependent primitives are still rejected by
`continuingStep?` until their source-facing interaction semantics are wired in.
-/
def sourceContinuingStep? (op : Structured.BasicOp) :
    Option Assembly.PrimStep :=
  match op with
  | .dup1 | .dup2 | .dup3 | .dup4
  | .dup5 | .dup6 | .dup7 | .dup8
  | .dup9 | .dup10 | .dup11 | .dup12
  | .dup13 | .dup14 | .dup15 | .dup16
  | .swap1 | .swap2 | .swap3 | .swap4
  | .swap5 | .swap6 | .swap7 | .swap8
  | .swap9 | .swap10 | .swap11 | .swap12
  | .swap13 | .swap14 | .swap15 | .swap16 => none
  | op => op.toPrimOp.continuingStep?

/--
Canonical source primitive semantics for the compiler tower.

It runs the already-verified structured/EVM primitive on an isolated concrete
stack containing exactly the source arguments, then projects the resulting
shared state and produced stack values back to the stack-free locals source
interpreter. This definition is deliberately not a proof shortcut: the lowering
proof must still show that running the same primitive inside an arbitrary caller
stack/frame has the same projected behavior.
-/
def structured : PrimitiveSemantics where
  eval op shared values :=
    if values.length = Expressions.Structured.BasicOp.inputs op then
    let state : EVMState :=
      { toSharedState := shared,
        pc := EvmYul.UInt256.ofNat 0,
        stack := values.reverse,
        execLength := 0 }
    match sourceContinuingStep? op with
    | none => .error .InvalidInstruction
    | some step =>
    match step.run state with
    | .ok state' => .ok (state'.toSharedState, state'.stack.reverse)
    | .error err => .error err
    else
      .error .StackUnderflow
  terminal kind shared values :=
    let state : EVMState :=
      { toSharedState := shared,
        pc := EvmYul.UInt256.ofNat 0,
        stack := values.reverse,
        execLength := 0 }
    match Structured.Terminal.step kind state with
    | .ok state' => .ok state'.toSharedState
    | .error err => .error err

end PrimitiveSemantics

structure Ctx where
  scope : List Name := []
  breakScope? : Option (List Name) := none
  continueScope? : Option (List Name) := none
  leaveScope? : Option (List Name) := none

namespace Ctx

def initial : Ctx := {}

def withoutLoopControl (ctx : Ctx) : Ctx :=
  { ctx with breakScope? := none, continueScope? := none }

def withLoopControl (ctx : Ctx) (breakScope continueScope : List Name) :
    Ctx :=
  { scope := ctx.scope,
    breakScope? := some breakScope,
    continueScope? := some continueScope,
    leaveScope? := ctx.leaveScope? }

def withLeaveScope (ctx : Ctx) (leaveScope : List Name) : Ctx :=
  { ctx with leaveScope? := some leaveScope }

end Ctx

abbrev invalid {α : Type} : Except EVMException α :=
  EvmCompiler.Structured.invalid

inductive Mode where
  | regular
  | brk
  | cont
  | leave
  | halt (kind : Assembly.HaltKind)
  deriving DecidableEq

structure Outcome where
  state : State
  mode : Mode

namespace Outcome

def regular (state : State) : Outcome :=
  { state := state, mode := .regular }

def brk (state : State) : Outcome :=
  { state := state, mode := .brk }

def cont (state : State) : Outcome :=
  { state := state, mode := .cont }

def leave (state : State) : Outcome :=
  { state := state, mode := .leave }

def halt (kind : Assembly.HaltKind) (state : State) : Outcome :=
  { state := state, mode := .halt kind }

end Outcome

namespace Expr

mutual
  def eval {results : Nat} (prim : PrimitiveSemantics)
      (expr : Expr results) (state : State) :
      Except EVMException (State × List Word) :=
    match expr with
    | .lit value =>
        .ok (state, [value])
    | .var name =>
        match state.vars name with
        | some value => .ok (state, [value])
        | none => invalid
    | .code code =>
        invalid
    | .prim op args => do
        let (stateAfterArgs, values) ← ExprSeq.eval prim args state
        let (shared, values') ← prim.eval op stateAfterArgs.shared values
        .ok (stateAfterArgs.withShared shared, values')

  def ExprSeq.eval {results : Nat} (prim : PrimitiveSemantics)
      (exprs : ExprSeq results) (state : State) :
      Except EVMException (State × List Word) :=
    match exprs with
    | .nil => .ok (state, [])
    | .cons head tail => do
        let (stateAfterHead, headValues) ← eval prim head state
        let (stateAfterTail, tailValues) ← ExprSeq.eval prim tail stateAfterHead
        .ok (stateAfterTail, headValues ++ tailValues)
end

def evalOne {results : Nat} (prim : PrimitiveSemantics)
    (expr : Expr results) (state : State) :
    Except EVMException (State × Word) := do
  let (state', values) ← eval prim expr state
  match values with
  | [value] => .ok (state', value)
  | _ => invalid

def evalCondition (prim : PrimitiveSemantics) (expr : Expr 1)
    (state : State) :
    Except EVMException (State × Bool) := do
  let (state', value) ← evalOne prim expr state
  .ok (state', value != EvmYul.UInt256.ofNat 0)

mutual
  theorem eval_vars_eq {results : Nat} {prim : PrimitiveSemantics}
      {expr : Expr results} {state state' : State} {values : List Word}
      (hEval : eval prim expr state = .ok (state', values)) :
      state'.vars = state.vars := by
    cases expr with
    | lit value =>
        simp [eval] at hEval
        rcases hEval with ⟨hState, _hValues⟩
        cases hState
        rfl
    | var name =>
        cases hLookup : state.vars name with
        | none =>
            simp [eval, hLookup, invalid, Structured.invalid] at hEval
        | some value =>
            simp [eval, hLookup] at hEval
            rcases hEval with ⟨hState, _hValues⟩
            cases hState
            rfl
    | code code =>
        simp [eval, invalid, Structured.invalid] at hEval
    | prim op args =>
        cases hArgs : ExprSeq.eval prim args state with
        | error err =>
            simp [eval, hArgs] at hEval
        | ok argsResult =>
            rcases argsResult with ⟨stateAfterArgs, values⟩
            cases hPrim :
                prim.eval op stateAfterArgs.shared values with
            | error err =>
                simp [eval, hArgs, hPrim] at hEval
            | ok primResult =>
                rcases primResult with ⟨sharedAfter, values'⟩
                simp [eval, hArgs, hPrim] at hEval
                rcases hEval with ⟨hState, _hValues⟩
                cases hState
                simpa [State.withShared] using
                  (evalSeq_vars_eq (prim := prim) (exprs := args)
                    (state := state) (state' := stateAfterArgs)
                    (values := values) hArgs)

  theorem evalSeq_vars_eq {results : Nat} {prim : PrimitiveSemantics}
      {exprs : ExprSeq results} {state state' : State} {values : List Word}
      (hEval : ExprSeq.eval prim exprs state = .ok (state', values)) :
      state'.vars = state.vars := by
    cases exprs with
    | nil =>
        simp [ExprSeq.eval] at hEval
        rcases hEval with ⟨hState, _hValues⟩
        cases hState
        rfl
    | cons head tail =>
        cases hHead : eval prim head state with
        | error err =>
            simp [ExprSeq.eval, hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨stateAfterHead, headValues⟩
            cases hTail :
                ExprSeq.eval prim tail stateAfterHead with
            | error err =>
                simp [ExprSeq.eval, hHead, hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨stateAfterTail, tailValues⟩
                simp [ExprSeq.eval, hHead, hTail] at hEval
                rcases hEval with ⟨hState, _hValues⟩
                have hHeadVars :
                    stateAfterHead.vars = state.vars :=
                  eval_vars_eq (prim := prim) (expr := head)
                    (state := state) (state' := stateAfterHead)
                    (values := headValues) hHead
                have hTailVars :
                    stateAfterTail.vars = stateAfterHead.vars :=
                  evalSeq_vars_eq (prim := prim) (exprs := tail)
                    (state := stateAfterHead) (state' := stateAfterTail)
                    (values := tailValues) hTail
                cases hState
                exact hTailVars.trans hHeadVars
end

theorem evalOne_vars_eq {results : Nat} {prim : PrimitiveSemantics}
    {expr : Expr results} {state state' : State} {value : Word}
    (hEval : evalOne prim expr state = .ok (state', value)) :
    state'.vars = state.vars := by
  unfold evalOne at hEval
  cases hExpr : eval prim expr state with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨stateAfter, values⟩
      cases values with
      | nil =>
          simp [hExpr, invalid, Structured.invalid] at hEval
      | cons head tail =>
          cases tail with
          | nil =>
              simp [hExpr] at hEval
              rcases hEval with ⟨hState, _hValue⟩
              cases hState
              exact eval_vars_eq hExpr
          | cons second rest =>
              simp [hExpr, invalid, Structured.invalid] at hEval

end Expr

namespace Switch

def select (scrutinee : Word) :
    List (Word × Block) → Option Block → Option Block
  | [], defaultBody => defaultBody
  | (value, body) :: rest, defaultBody =>
      if value = scrutinee then
        some body
      else
        select scrutinee rest defaultBody

theorem property_of_select
    {motive : Block → Prop}
    {scrutinee : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {selected : Block}
    (hCases :
      ∀ value body, (value, body) ∈ cases → motive body)
    (hDefault :
      ∀ body, defaultBody = some body → motive body)
    (hSelect : select scrutinee cases defaultBody = some selected) :
    motive selected := by
  induction cases with
  | nil =>
      exact hDefault selected hSelect
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      by_cases hMatch : value = scrutinee
      · simp [select, hMatch] at hSelect
        subst selected
        exact hCases value body (by simp)
      · simp [select, hMatch] at hSelect
        apply ih
        · intro restValue restBody hMem
          exact hCases restValue restBody (by simp [hMem])
        · exact hSelect

end Switch

mutual
  def Block.runOpen (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) : Nat → Block → State →
      Except EVMException (Outcome × Ctx)
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ← Stmt.run prim program ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen prim program ctx' fuel { stmts := rest }
              outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) (block : Block) (fuel : Nat) (state : State) :
      Except EVMException Outcome := do
    let (outcome, _) ← Block.runOpen prim program ctx fuel block state
    match outcome.mode with
    | .regular =>
        .ok (Outcome.regular (outcome.state.restrictTo ctx.scope))
    | .brk | .cont | .leave | .halt _ =>
        .ok outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def Stmt.runForLoop (prim : PrimitiveSemantics) (program : Program)
      (loopCtx : Ctx) (cond : Expr 1) (postBase : Ctx) (post : Block)
      (bodyBase : Ctx) (body : Block) :
      Nat → State → Except EVMException Outcome
    | 0, _state =>
        invalid
    | fuel + 1, state =>
        match Expr.evalCondition prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.runScoped prim program bodyBase body fuel
                  stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.runScoped prim program postBase post fuel
                          bodyOutcome.state with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop prim program loopCtx cond
                                postBase post bodyBase body fuel
                                postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Outcome.regular (stateAfterCond.restrictTo loopCtx.scope))
  termination_by fuel _state => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run (prim : PrimitiveSemantics) (program : Program) (ctx : Ctx) :
      Nat → Stmt → State → Except EVMException (Outcome × Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ← Expr.eval prim expr state
        .ok (Outcome.regular state', ctx)
    | _fuel, .exprs exprs, state => do
        let (state', _values) ← Expr.ExprSeq.eval prim exprs state
        .ok (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ← Expr.evalOne prim value state
        .ok (Outcome.regular (stateAfterValue.insert name value'),
          { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if state.vars.contains name then
          let (stateAfterValue, value') ← Expr.evalOne prim value state
          .ok (Outcome.regular
            (stateAfterValue.withVars
              (Store.insert stateAfterValue.vars name value')), ctx)
        else
          invalid
    | _fuel, .assignTop _name, _state =>
        invalid
    | _fuel, .assignTopWithOffset _offset _name, _state =>
        invalid
    | _fuel, .promoteName _name, _state =>
        invalid
    | _fuel, .cleanupTo _targetLayout, _state =>
        invalid
    | fuel, .block body, state => do
        let outcome ← Block.runScoped prim program ctx body fuel state
        .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        invalid
    | fuel + 1, .if_ cond body, state =>
        match Expr.evalCondition prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then do
              let outcome ← Block.runScoped prim program ctx body fuel
                stateAfterCond
              .ok (outcome, ctx)
            else
              .ok (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let (stateAfterScrutinee, value) ← Expr.evalOne prim scrutinee state
        match Switch.select value cases defaultBody with
        | none => .ok (Outcome.regular stateAfterScrutinee, ctx)
        | some body =>
            let outcome ← Block.runScoped prim program ctx body fuel
              stateAfterScrutinee
            .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx) ←
          Block.runOpen prim program initBase fuel init state
        match initOutcome.mode with
        | .regular =>
            let loopCtx := initCtx
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.scope initCtx.scope
            let loopOutcome ←
              Stmt.runForLoop prim program loopCtx cond postBase post
                bodyBase body fuel initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                .ok (Outcome.regular (loopOutcome.state.restrictTo ctx.scope),
                  ctx)
            | .brk | .cont =>
                invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx)
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx)
    | _fuel, .brk, state =>
        match ctx.breakScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.brk (state.restrictTo scope), ctx)
    | _fuel, .cont, state =>
        match ctx.continueScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.cont (state.restrictTo scope), ctx)
    | _fuel, .leave, state =>
        match ctx.leaveScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.leave (state.restrictTo scope), ctx)
    | _fuel, .call _name, _state =>
        invalid
    | _fuel, .terminal kind, state => do
        let shared ← prim.terminal kind state.shared []
        .ok (Outcome.halt kind (state.withShared shared), ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ← Expr.ExprSeq.eval prim args state
        let shared ← prim.terminal kind stateAfterArgs.shared values
        .ok (Outcome.halt kind (stateAfterArgs.withShared shared), ctx)
  termination_by fuel stmt _state => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Stmt

theorem run_regular_scope {prim : PrimitiveSemantics} {program : Program}
    {ctx ctx' : Ctx} {fuel : Nat} {stmt : Stmt} {state out : State}
    (hRun :
      Source.Stmt.run prim program ctx fuel stmt state =
        .ok (Outcome.regular out, ctx')) :
    ctx'.scope = Scope.Stmt.outEnv ctx.scope stmt := by
  cases stmt with
  | expr expr =>
      cases hEval : Expr.eval prim expr state with
      | error err =>
          simp [Source.Stmt.run, hEval] at hRun
      | ok result =>
          rcases result with ⟨stateAfterExpr, values⟩
          simp [Source.Stmt.run, hEval, Scope.Stmt.outEnv] at hRun
          rcases hRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          rfl
  | exprs exprs =>
      cases hEval : Expr.ExprSeq.eval prim exprs state with
      | error err =>
          simp [Source.Stmt.run, hEval] at hRun
      | ok result =>
          rcases result with ⟨stateAfterExprs, values⟩
          simp [Source.Stmt.run, hEval, Scope.Stmt.outEnv] at hRun
          rcases hRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          rfl
  | let_ name value =>
      cases hEval : Expr.evalOne prim value state with
      | error err =>
          simp [Source.Stmt.run, hEval] at hRun
      | ok result =>
          rcases result with ⟨stateAfterValue, value'⟩
          simp [Source.Stmt.run, hEval, Scope.Stmt.outEnv] at hRun
          rcases hRun with ⟨_hOutcome, hCtxEq⟩
          cases hCtxEq
          rfl
  | assign name value =>
      cases hContains : state.vars.contains name with
      | false =>
          simp [Source.Stmt.run, hContains, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | true =>
          cases hEval : Expr.evalOne prim value state with
          | error err =>
              simp [Source.Stmt.run, hContains, hEval] at hRun
          | ok result =>
              rcases result with ⟨stateAfterValue, value'⟩
              simp [Source.Stmt.run, hContains, hEval, Scope.Stmt.outEnv]
                at hRun
              rcases hRun with ⟨_hOutcome, hCtxEq⟩
              cases hCtxEq
              rfl
  | assignTop name =>
      simp [Source.Stmt.run, Source.invalid, invalid, EvmCompiler.Structured.invalid] at hRun
  | assignTopWithOffset offset name =>
      simp [Source.Stmt.run, Source.invalid, invalid, EvmCompiler.Structured.invalid] at hRun
  | promoteName name =>
      simp [Source.Stmt.run, Source.invalid, invalid, EvmCompiler.Structured.invalid] at hRun
  | cleanupTo targetLayout =>
      simp [Source.Stmt.run, Source.invalid, invalid,
        EvmCompiler.Structured.invalid] at hRun
  | block body =>
      cases hBlock : Block.runScoped prim program ctx body fuel state with
      | error err =>
          simp [Source.Stmt.run, hBlock] at hRun
      | ok outcome =>
          cases outcome with
          | mk blockState mode =>
              cases mode <;> simp [Source.Stmt.run, hBlock,
                Scope.Stmt.outEnv, Outcome.regular, Outcome.brk,
                Outcome.cont, Outcome.leave, Outcome.halt] at hRun
              case regular =>
                rcases hRun with ⟨_hOutcome, hCtxEq⟩
                cases hCtxEq
                rfl
  | if_ cond body =>
      cases fuel with
      | zero =>
          simp [Source.Stmt.run, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | succ fuel =>
          cases hCond : Expr.evalCondition prim cond state with
          | error err =>
              simp [Source.Stmt.run, hCond] at hRun
          | ok condResult =>
              rcases condResult with ⟨stateAfterCond, condTrue⟩
              cases condTrue <;>
                simp [Source.Stmt.run, hCond, Scope.Stmt.outEnv] at hRun
              · rcases hRun with ⟨_hOutcome, hCtxEq⟩
                cases hCtxEq
                rfl
              · cases hBlock :
                    Block.runScoped prim program ctx body fuel
                      stateAfterCond with
                | error err =>
                    simp [hBlock] at hRun
                | ok outcome =>
                    cases outcome with
                    | mk blockState mode =>
                        cases mode <;> simp [hBlock, Outcome.regular,
                          Outcome.brk, Outcome.cont, Outcome.leave,
                          Outcome.halt] at hRun
                        case regular =>
                          rcases hRun with ⟨_hOutcome, hCtxEq⟩
                          cases hCtxEq
                          rfl
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          simp [Source.Stmt.run, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | succ fuel =>
          cases hScrutinee : Expr.evalOne prim scrutinee state with
          | error err =>
              simp [Source.Stmt.run, hScrutinee] at hRun
          | ok scrutineeResult =>
              rcases scrutineeResult with ⟨stateAfterScrutinee, value⟩
              cases hSelect : Switch.select value cases defaultBody with
              | none =>
                  simp [Source.Stmt.run, hScrutinee, hSelect,
                    Scope.Stmt.outEnv] at hRun
                  rcases hRun with ⟨_hOutcome, hCtxEq⟩
                  cases hCtxEq
                  rfl
              | some body =>
                  cases hBlock :
                      Block.runScoped prim program ctx body fuel
                        stateAfterScrutinee with
                  | error err =>
                      simp [Source.Stmt.run, hScrutinee, hSelect, hBlock]
                        at hRun
                  | ok outcome =>
                      cases outcome with
                      | mk blockState mode =>
                          cases mode <;> simp [Source.Stmt.run, hScrutinee,
                            hSelect, hBlock, Scope.Stmt.outEnv,
                            Outcome.regular, Outcome.brk, Outcome.cont,
                            Outcome.leave, Outcome.halt] at hRun
                          case regular =>
                            rcases hRun with ⟨_hOutcome, hCtxEq⟩
                            cases hCtxEq
                            rfl
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          simp [Source.Stmt.run, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | succ fuel =>
          cases hInit :
              Block.runOpen prim program ctx.withoutLoopControl fuel init
                state with
          | error err =>
              simp [Source.Stmt.run, hInit] at hRun
          | ok initResult =>
              rcases initResult with ⟨initOutcome, initCtx⟩
              cases initOutcome with
              | mk initState initMode =>
                  cases initMode <;> simp [Source.Stmt.run, hInit,
                    Scope.Stmt.outEnv, Outcome.regular, Outcome.brk,
                    Outcome.cont, Outcome.leave, Outcome.halt,
                Source.invalid, invalid, EvmCompiler.Structured.invalid] at hRun
                  case regular =>
                    cases hLoop :
                        Stmt.runForLoop prim program initCtx cond
                          initCtx.withoutLoopControl post
                          (initCtx.withLoopControl initCtx.scope initCtx.scope)
                          body fuel initState with
                    | error err =>
                        simp [hLoop] at hRun
                    | ok loopOutcome =>
                        cases loopOutcome with
                        | mk loopState loopMode =>
                            cases loopMode <;> simp [hLoop, Outcome.regular,
                              Outcome.brk, Outcome.cont, Outcome.leave,
                              Outcome.halt, Source.invalid, invalid,
                              EvmCompiler.Structured.invalid] at hRun
                            case regular =>
                              rcases hRun with ⟨_hOutcome, hCtxEq⟩
                              cases hCtxEq
                              rfl
  | brk =>
      cases hBreak : ctx.breakScope? with
      | none =>
          simp [Source.Stmt.run, hBreak, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | some scope =>
          simp [Source.Stmt.run, hBreak, Outcome.brk] at hRun
          exact False.elim (by
            rcases hRun with ⟨hOutcome, _hCtx⟩
            cases hOutcome)
  | cont =>
      cases hContinue : ctx.continueScope? with
      | none =>
          simp [Source.Stmt.run, hContinue, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | some scope =>
          simp [Source.Stmt.run, hContinue, Outcome.cont] at hRun
          exact False.elim (by
            rcases hRun with ⟨hOutcome, _hCtx⟩
            cases hOutcome)
  | leave =>
      cases hLeave : ctx.leaveScope? with
      | none =>
          simp [Source.Stmt.run, hLeave, Source.invalid, invalid,
            EvmCompiler.Structured.invalid] at hRun
      | some scope =>
          simp [Source.Stmt.run, hLeave, Outcome.leave] at hRun
          exact False.elim (by
            rcases hRun with ⟨hOutcome, _hCtx⟩
            cases hOutcome)
  | call name =>
      simp [Source.Stmt.run, Source.invalid, invalid, EvmCompiler.Structured.invalid] at hRun
  | terminal kind =>
      cases hTerminal : prim.terminal kind state.shared [] with
      | error err =>
          simp [Source.Stmt.run, hTerminal] at hRun
      | ok shared =>
          simp [Source.Stmt.run, hTerminal, Outcome.halt] at hRun
          exact False.elim (by
            rcases hRun with ⟨hOutcome, _hCtx⟩
            cases hOutcome)
  | terminalArgs kind args =>
      cases hArgs : Expr.ExprSeq.eval prim args state with
      | error err =>
          simp [Source.Stmt.run, hArgs] at hRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, values⟩
          cases hTerminal : prim.terminal kind stateAfterArgs.shared values with
          | error err =>
              simp [Source.Stmt.run, hArgs, hTerminal] at hRun
          | ok shared =>
              simp [Source.Stmt.run, hArgs, hTerminal, Outcome.halt] at hRun
              exact False.elim (by
                rcases hRun with ⟨hOutcome, _hCtx⟩
                cases hOutcome)

end Stmt

namespace Block

theorem runOpen_regular_scope {prim : PrimitiveSemantics}
    {program : Program} {ctx ctx' : Ctx} {fuel : Nat} {block : Block}
    {state out : State}
    (hRun :
      Source.Block.runOpen prim program ctx fuel block state =
        .ok (Outcome.regular out, ctx')) :
    ctx'.scope = Scope.Block.outEnv ctx.scope block := by
  cases block with
  | mk stmts =>
      induction stmts generalizing ctx ctx' fuel state out with
      | nil =>
          cases fuel with
          | zero =>
              simp [Source.Block.runOpen, Source.invalid, invalid,
                EvmCompiler.Structured.invalid] at hRun
          | succ fuel =>
              simp [Source.Block.runOpen, Scope.Block.outEnv,
                Scope.StmtList.outEnv] at hRun
              rcases hRun with ⟨_hOutcome, hCtxEq⟩
              cases hCtxEq
              rfl
      | cons stmt rest ih =>
          cases fuel with
          | zero =>
              simp [Source.Block.runOpen, Source.invalid, invalid,
                EvmCompiler.Structured.invalid] at hRun
          | succ fuel =>
              cases hStmt :
                  Source.Stmt.run prim program ctx fuel stmt state with
              | error err =>
                  simp [Source.Block.runOpen, hStmt] at hRun
              | ok stmtResult =>
                  rcases stmtResult with ⟨stmtOutcome, headCtx⟩
                  cases stmtOutcome with
                  | mk stmtState mode =>
                      cases mode <;> simp [Source.Block.runOpen, hStmt,
                        Outcome.regular, Outcome.brk, Outcome.cont,
                        Outcome.leave, Outcome.halt] at hRun
                      case regular =>
                        have hHeadScope :
                            headCtx.scope =
                              Scope.Stmt.outEnv ctx.scope stmt :=
                          Stmt.run_regular_scope hStmt
                        have hTailScope :
                            ctx'.scope =
                              Scope.Block.outEnv headCtx.scope
                                { stmts := rest } :=
                          ih hRun
                        simpa [Scope.Block.outEnv, Scope.StmtList.outEnv,
                          hHeadScope] using hTailScope
                      all_goals
                        exact False.elim (by
                          rcases hRun with ⟨hOutcome, _hCtx⟩
                          cases hOutcome)

theorem runScoped_regular_eq_restrict {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {block : Block} {fuel : Nat}
    {state out : State}
    (hRun :
      Block.runScoped prim program ctx block fuel state =
        .ok (Outcome.regular out)) :
    ∃ inner finalCtx,
      Block.runOpen prim program ctx fuel block state =
        .ok (Outcome.regular inner, finalCtx) ∧
        out = inner.restrictTo ctx.scope := by
  unfold Block.runScoped at hRun
  cases hOpen : Block.runOpen prim program ctx fuel block state with
  | error err =>
      simp [hOpen] at hRun
  | ok result =>
      rcases result with ⟨outcome, finalCtx⟩
      cases outcome with
      | mk outcomeState mode =>
          cases mode
          · simp [hOpen, Outcome.regular] at hRun
            cases hRun
            refine ⟨outcomeState, finalCtx, ?_, rfl⟩
            simpa [Outcome.regular] using hOpen
          · simp [hOpen, Outcome.regular, Outcome.brk] at hRun
          · simp [hOpen, Outcome.regular, Outcome.cont] at hRun
          · simp [hOpen, Outcome.regular, Outcome.leave] at hRun
          · simp [hOpen, Outcome.regular, Outcome.halt] at hRun

theorem runScoped_regular_drops_not_mem {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {block : Block} {fuel : Nat}
    {state out : State} {name : Name}
    (hRun :
      Block.runScoped prim program ctx block fuel state =
        .ok (Outcome.regular out))
    (hNotMem : name ∉ ctx.scope) :
    out.vars name = none := by
  rcases runScoped_regular_eq_restrict hRun with
    ⟨inner, _finalCtx, _hOpen, hOut⟩
  rw [hOut]
  exact Store.restrictTo_not_mem hNotMem

end Block

namespace Program

def initialState (shared : EvmYul.SharedState .EVM) : State :=
  { shared := shared, vars := Store.empty }

def runState (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : State) : Except EVMException Outcome :=
  Block.runScoped prim program Ctx.initial program.body fuel state

def run (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : EVMState) : Except EVMException Outcome :=
  runState prim fuel program (initialState state.toSharedState)

inductive Eval (prim : PrimitiveSemantics) :
    Nat → Program → State → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : State}
      {outcome : Outcome}
      (hRun : runState prim fuel program initial = .ok outcome) :
      Eval prim fuel program initial outcome

end Program

mutual
  def Expr.SourceOwned {results : Nat} (expr : Expr results) : Prop :=
    match expr with
    | .lit _value => True
    | .var _name => True
    | .code _code => False
    | .prim _op args => ExprSeq.SourceOwned args

  def ExprSeq.SourceOwned {results : Nat} (exprs : ExprSeq results) : Prop :=
    match exprs with
    | .nil => True
    | .cons head tail =>
        Expr.SourceOwned head ∧ ExprSeq.SourceOwned tail
end

mutual
  def Block.SourceOwned : Block → Prop
    | ⟨stmts⟩ => StmtList.SourceOwned stmts

  def Stmt.SourceOwned : Stmt → Prop
    | .expr (results := results) expr =>
        results = 0 ∧ Expr.SourceOwned expr
    | .exprs _exprs => False
    | .let_ _name value => Expr.SourceOwned value
    | .assign _name value => Expr.SourceOwned value
    | .assignTop _name => False
    | .assignTopWithOffset _offset _name => False
    | .promoteName _name => False
    | .cleanupTo _targetLayout => False
    | .block body => Block.SourceOwned body
    | .if_ cond body => Expr.SourceOwned cond ∧ Block.SourceOwned body
    | .switch scrutinee cases defaultBody =>
        Expr.SourceOwned scrutinee ∧ CaseList.SourceOwned cases ∧
          (match defaultBody with
          | none => True
          | some body => Block.SourceOwned body)
    | .for_ init cond post body =>
        Block.SourceOwned init ∧ Expr.SourceOwned cond ∧
          Block.SourceOwned post ∧ Block.SourceOwned body
    | .brk | .cont | .leave => True
    | .call _name => False
    | .terminal kind => kind.argCount = 0
    | .terminalArgs _kind args => ExprSeq.SourceOwned args

  def StmtList.SourceOwned : List Stmt → Prop
    | [] => True
    | stmt :: rest => Stmt.SourceOwned stmt ∧ StmtList.SourceOwned rest

  def CaseList.SourceOwned : List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest => Block.SourceOwned body ∧
        CaseList.SourceOwned rest
end

namespace CaseList

theorem sourceOwned_of_mem
    {cases : List (Word × Block)}
    {value : Word} {body : Block}
    (hOwned : SourceOwned cases)
    (hMem : (value, body) ∈ cases) :
    Block.SourceOwned body := by
  induction cases with
  | nil => simp at hMem
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      rcases hOwned with ⟨hHead, hRest⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hEq | hMem
      · rcases hEq with ⟨rfl, rfl⟩
        exact hHead
      · exact ih hRest hMem

end CaseList

namespace Switch

theorem case_sourceOwned_of_mem
    {scrutinee : Expr 1}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {value : Word} {body : Block}
    (hOwned : Stmt.SourceOwned (.switch scrutinee cases defaultBody))
    (hMem : (value, body) ∈ cases) :
    Block.SourceOwned body := by
  cases defaultBody with
  | none =>
      exact CaseList.sourceOwned_of_mem hOwned.2.1 hMem
  | some default =>
      exact CaseList.sourceOwned_of_mem hOwned.2.1 hMem

theorem default_sourceOwned_of_eq
    {scrutinee : Expr 1}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {body : Block}
    (hOwned : Stmt.SourceOwned (.switch scrutinee cases defaultBody))
    (hDefault : defaultBody = some body) :
    Block.SourceOwned body := by
  subst defaultBody
  exact hOwned.2.2

end Switch

def Program.SourceOwned (program : Program) : Prop :=
  program.procs = [] ∧ Block.SourceOwned program.body

def Expr.SourceWF {results : Nat} (env : List Name)
    (expr : Expr results) : Prop :=
  Expr.SourceOwned expr ∧ Lexical.ExprScoped env expr

def ExprSeq.SourceWF {results : Nat} (env : List Name)
    (exprs : ExprSeq results) : Prop :=
  ExprSeq.SourceOwned exprs ∧ Lexical.ExprSeqScoped env exprs

def Block.SourceWF (env : List Name) (block : Block) : Prop :=
  Block.SourceOwned block ∧ Lexical.BlockScoped env block

def Stmt.SourceWF (env : List Name) (stmt : Stmt) : Prop :=
  Stmt.SourceOwned stmt ∧ Lexical.StmtScoped env stmt

def StmtList.SourceWF (env : List Name) (stmts : List Stmt) : Prop :=
  StmtList.SourceOwned stmts ∧ Lexical.StmtListScoped env stmts

def Program.SourceWF (program : Program) : Prop :=
  program.procs = [] ∧ Block.SourceWF [] program.body

namespace Program

theorem sourceOwned_of_sourceWF {program : Program}
    (hWF : SourceWF program) :
    SourceOwned program := by
  rcases hWF with ⟨hProcs, hBody⟩
  exact ⟨hProcs, hBody.1⟩

theorem lexicalScoped_of_sourceWF {program : Program}
    (hWF : SourceWF program) :
    Lexical.ProgramScoped program := by
  exact hWF.2.2

end Program

end Source

end Locals
end EvmCompiler
