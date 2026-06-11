import EvmCompiler.Functions.SourceSemantics
import EvmCompiler.Locals.EffectSemantics

namespace EvmCompiler
namespace Functions
namespace Source
namespace Effectful

/-!
Effect-carrying semantics for the function-aware source language.

The extra state is preserved across function entry and return. Only the
underlying `Locals.Source.State` is replaced when creating a function-local
store or restoring the caller store, so transcript cursors and future effects
do not need a second Functions evaluator.
-/

abbrev StateModel := Locals.Source.Effectful.StateModel
abbrev PrimitiveSemantics := Locals.Source.Effectful.PrimitiveSemantics
abbrev Outcome := Locals.Source.Effectful.Outcome

namespace Outcome

def regular {σ : Type} (state : σ) : Outcome σ :=
  Locals.Source.Effectful.Outcome.regular state

def brk {σ : Type} (state : σ) : Outcome σ :=
  Locals.Source.Effectful.Outcome.brk state

def cont {σ : Type} (state : σ) : Outcome σ :=
  Locals.Source.Effectful.Outcome.cont state

def leave {σ : Type} (state : σ) : Outcome σ :=
  Locals.Source.Effectful.Outcome.leave state

def halt {σ : Type} (kind : Assembly.HaltKind) (state : σ) : Outcome σ :=
  Locals.Source.Effectful.Outcome.halt kind state

end Outcome

namespace Expr

abbrev eval {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Functions.Expr results)
    (state : σ) : Except EVMException (σ × List Word) :=
  Locals.Source.Effectful.Expr.eval model prim expr state

abbrev evalOne {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Functions.Expr results)
    (state : σ) : Except EVMException (σ × Word) :=
  Locals.Source.Effectful.Expr.evalOne model prim expr state

abbrev evalCondition {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Functions.Expr 1)
    (state : σ) : Except EVMException (σ × Bool) :=
  Locals.Source.Effectful.Expr.evalCondition model prim expr state

end Expr

namespace ArgList

def eval {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) :
    List (Functions.Expr 1) → σ →
      Except EVMException (σ × List Word)
  | [], state => .ok (state, [])
  | arg :: rest, state => do
      let (stateAfterArg, value) ← Expr.evalOne model prim arg state
      let (stateAfterRest, values) ←
        eval model prim rest stateAfterArg
      .ok (stateAfterRest, value :: values)

end ArgList

inductive CallResult (σ : Type) where
  | returned (state : σ) (values : List Word)
  | halted (kind : Assembly.HaltKind) (state : σ)

mutual
  def Block.runOpen {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Functions.Program)
      (ctx : Source.Ctx) : Nat → Functions.Block → σ →
      Except EVMException (Outcome σ × Source.Ctx)
    | 0, _block, _state =>
        Source.invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ←
          Stmt.run model prim program ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen model prim program ctx' fuel
              { stmts := rest } outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Functions.Program)
      (ctx : Source.Ctx) (block : Functions.Block) (fuel : Nat)
      (state : σ) : Except EVMException (Outcome σ) := do
    let (outcome, _) ←
      Block.runOpen model prim program ctx fuel block state
    match outcome.mode with
    | .regular =>
        .ok (Outcome.regular (model.restrictTo ctx.scope outcome.state))
    | .brk | .cont | .leave | .halt _ =>
        .ok outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def FunDef.runBody {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Functions.Program)
      (fn : Functions.FunDef) (args : List Word) :
      Nat → σ → Except EVMException (CallResult σ)
    | 0, _state =>
        Source.invalid
    | fuel + 1, state => do
        let paramStore ←
          (Source.Store.insertMany fn.params args
            Locals.Source.Store.empty).elim Source.invalid pure
        let initialStore := Source.Store.initReturns fn.returns paramStore
        let callerSource := model.source state
        let initialSource : Locals.Source.State :=
          { shared := callerSource.shared, vars := initialStore }
        let initialState := model.withSource state initialSource
        let functionScope := fn.returns ++ fn.params
        let bodyCtx := Source.Ctx.initial.withLeaveScope functionScope
        let bodyCtx := { bodyCtx with scope := functionScope }
        let (bodyOutcome, _bodyFinalCtx) ←
          Block.runOpen model prim program bodyCtx fuel fn.body initialState
        match bodyOutcome.mode with
        | .regular | .leave =>
            let values ←
              (Source.Store.lookupMany fn.returns
                (model.vars bodyOutcome.state)).elim Source.invalid pure
            .ok (.returned bodyOutcome.state values)
        | .brk | .cont =>
            Source.invalid
        | .halt kind =>
            .ok (.halted kind bodyOutcome.state)
  termination_by fuel _state => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runForLoop {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Functions.Program)
      (loopCtx : Source.Ctx) (cond : Functions.Expr 1)
      (postBase : Source.Ctx) (post : Functions.Block)
      (bodyBase : Source.Ctx) (body : Functions.Block) :
      Nat → σ → Except EVMException (Outcome σ)
    | 0, _state =>
        Source.invalid
    | fuel + 1, state =>
        match Expr.evalCondition model prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match
                  Block.runScoped model prim program bodyBase body fuel
                    stateAfterCond
              with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match
                          Block.runScoped model prim program postBase post fuel
                            bodyOutcome.state
                      with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop model prim program loopCtx cond
                                postBase post bodyBase body fuel
                                postOutcome.state
                          | .brk | .cont =>
                              Source.invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok
                (Outcome.regular
                  (model.restrictTo loopCtx.scope stateAfterCond))
  termination_by fuel _state => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Functions.Program)
      (ctx : Source.Ctx) : Nat → Functions.Stmt → σ →
      Except EVMException (Outcome σ × Source.Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ← Expr.eval model prim expr state
        .ok (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ←
          Expr.evalOne model prim value state
        .ok
          (Outcome.regular
            (model.insert stateAfterValue name value'),
            { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if model.vars state |>.contains name then
          let (stateAfterValue, value') ←
            Expr.evalOne model prim value state
          .ok
            (Outcome.regular
              (model.withVars stateAfterValue
                (Locals.Source.Store.insert
                  (model.vars stateAfterValue) name value')),
              ctx)
        else
          Source.invalid
    | fuel, .block body, state => do
        let outcome ←
          Block.runScoped model prim program ctx body fuel state
        .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        Source.invalid
    | fuel + 1, .if_ cond body, state =>
        match Expr.evalCondition model prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then do
              let outcome ←
                Block.runScoped model prim program ctx body fuel
                  stateAfterCond
              .ok (outcome, ctx)
            else
              .ok (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        Source.invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let (stateAfterScrutinee, value) ←
          Expr.evalOne model prim scrutinee state
        match Source.Switch.select value cases defaultBody with
        | none => .ok (Outcome.regular stateAfterScrutinee, ctx)
        | some body =>
            let outcome ←
              Block.runScoped model prim program ctx body fuel
                stateAfterScrutinee
            .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        Source.invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx) ←
          Block.runOpen model prim program initBase fuel init state
        match initOutcome.mode with
        | .regular =>
            let loopCtx := initCtx
            let postBase := initCtx.withoutLoopControl
            let bodyBase :=
              initCtx.withLoopControl initCtx.scope initCtx.scope
            let loopOutcome ←
              Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body fuel initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                .ok
                  (Outcome.regular
                    (model.restrictTo ctx.scope loopOutcome.state),
                    ctx)
            | .brk | .cont =>
                Source.invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx)
        | .brk | .cont =>
            Source.invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx)
    | _fuel, .brk, state =>
        match ctx.breakScope? with
        | none => Source.invalid
        | some scope =>
            .ok (Outcome.brk (model.restrictTo scope state), ctx)
    | _fuel, .cont, state =>
        match ctx.continueScope? with
        | none => Source.invalid
        | some scope =>
            .ok (Outcome.cont (model.restrictTo scope state), ctx)
    | _fuel, .leave, state =>
        match ctx.leaveScope? with
        | none => Source.invalid
        | some scope =>
            .ok (Outcome.leave (model.restrictTo scope state), ctx)
    | 0, .call _targets _functionName _args, _state =>
        Source.invalid
    | fuel + 1, .call targets functionName args, state => do
        if targets.Nodup then
          let (stateAfterArgs, argValues) ←
            ArgList.eval model prim args state
          let fn ←
            (Source.FunList.find? functionName program.functions).elim
              Source.invalid pure
          let callResult ←
            FunDef.runBody model prim program fn argValues fuel
              stateAfterArgs
          match callResult with
          | .returned stateAfterCall returnValues =>
              let returnStore ←
                (Source.Store.assignMany targets returnValues
                  (model.vars stateAfterArgs)).elim Source.invalid pure
              let returnedSource := model.source stateAfterCall
              .ok
                (Outcome.regular
                  (model.withSource stateAfterCall
                    { shared := returnedSource.shared,
                      vars := returnStore }),
                  ctx)
          | .halted kind haltedState =>
              .ok (Outcome.halt kind haltedState, ctx)
        else
          Source.invalid
    | _fuel, .terminal kind, state => do
        let state' ← prim.terminal kind state []
        .ok (Outcome.halt kind state', ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ←
          Locals.Source.Effectful.Expr.ExprSeq.eval
            model prim args state
        let state' ← prim.terminal kind stateAfterArgs values
        .ok (Outcome.halt kind state', ctx)
  termination_by fuel stmt _state => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

def runState {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (program : Functions.Program) (state : σ) :
    Except EVMException (Outcome σ) :=
  Block.runScoped model prim program Source.Ctx.initial
    program.body fuel state

end Program

end Effectful
end Source
end Functions
end EvmCompiler
