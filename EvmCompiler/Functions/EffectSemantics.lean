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

def IsExit {σ : Type} (outcome : Outcome σ) : Prop :=
  match outcome.mode with
  | .leave | .halt _ => True
  | .regular | .brk | .cont => False

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

namespace Stmt

/--
Canonical loop execution when the current condition is false.
-/
theorem runForLoop_false_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, false)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok
        (Outcome.regular
          (model.restrictTo loopCtx.scope afterCond)) := by
  simp [Stmt.runForLoop, hCond, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Canonical source `for` execution whose initializer is regular and whose first
condition is false.
-/
theorem run_for_false_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source afterInit afterCond : σ}
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          (fuel + 1) init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hCond :
      Expr.evalCondition model prim cond afterInit =
        .ok (afterCond, false)) :
    Stmt.run model prim program ctx (fuel + 2)
        (.for_ init cond post body) source =
      .ok
        (Outcome.regular
          (model.restrictTo ctx.scope
            (model.restrictTo initCtx.scope afterCond)),
          ctx) := by
  simp [Stmt.run, hInit, Stmt.runForLoop, hCond, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Canonical loop execution when the condition is true and the body breaks.
-/
theorem runForLoop_body_brk_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
      .ok (Outcome.brk afterBody)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.regular afterBody) := by
  simp [Stmt.runForLoop, hCond, hBody, Outcome.brk,
    Locals.Source.Effectful.Outcome.brk]

/--
Canonical loop execution when the condition is true and the body leaves.
-/
theorem runForLoop_body_leave_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.leave afterBody)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.leave afterBody) := by
  simp [Stmt.runForLoop, hCond, hBody, Outcome.leave,
    Locals.Source.Effectful.Outcome.leave]

/--
Canonical loop execution when the condition is true and the body halts.
-/
theorem runForLoop_body_halt_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody : σ}
    {kind : Assembly.HaltKind}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.halt kind afterBody)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.halt kind afterBody) := by
  simp [Stmt.runForLoop, hCond, hBody, Outcome.halt,
    Locals.Source.Effectful.Outcome.halt]

/--
Canonical loop execution for one regular body/post iteration followed by a
recursive regular loop result.
-/
theorem runForLoop_regular_post_regular_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost final : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok (Outcome.regular final)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.regular final) := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, hLoop, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Canonical loop execution for a continuing body, regular post, and recursive
regular loop result.
-/
theorem runForLoop_cont_post_regular_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost final : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok (Outcome.regular final)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.regular final) := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, hLoop,
    Outcome.regular, Locals.Source.Effectful.Outcome.regular,
    Outcome.cont, Locals.Source.Effectful.Outcome.cont]

/--
Canonical loop execution for one regular body/post iteration followed by an
arbitrary recursive loop outcome.
-/
theorem runForLoop_regular_post_recurse_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost : σ}
    {outcome : Outcome σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok outcome) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok outcome := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, hLoop, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Canonical loop execution for a continuing body, regular post, and arbitrary
recursive loop outcome.
-/
theorem runForLoop_cont_post_recurse_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost : σ}
    {outcome : Outcome σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok outcome) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok outcome := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, hLoop,
    Outcome.regular, Locals.Source.Effectful.Outcome.regular,
    Outcome.cont, Locals.Source.Effectful.Outcome.cont]

/--
Canonical loop execution for a regular body followed by a leaving post.
-/
theorem runForLoop_regular_post_leave_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.leave afterPost)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.leave afterPost) := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular, Outcome.leave,
    Locals.Source.Effectful.Outcome.leave]

/--
Canonical loop execution for a continuing body followed by a leaving post.
-/
theorem runForLoop_cont_post_leave_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.leave afterPost)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.leave afterPost) := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, Outcome.cont,
    Locals.Source.Effectful.Outcome.cont, Outcome.leave,
    Locals.Source.Effectful.Outcome.leave]

/--
Canonical loop execution for a regular body followed by a halting post.
-/
theorem runForLoop_regular_post_halt_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost : σ}
    {kind : Assembly.HaltKind}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.halt kind afterPost)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.halt kind afterPost) := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular, Outcome.halt,
    Locals.Source.Effectful.Outcome.halt]

/--
Canonical loop execution for a continuing body followed by a halting post.
-/
theorem runForLoop_cont_post_halt_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source afterCond afterBody afterPost : σ}
    {kind : Assembly.HaltKind}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.halt kind afterPost)) :
    Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.halt kind afterPost) := by
  simp [Stmt.runForLoop, hCond, hBody, hPost, Outcome.cont,
    Locals.Source.Effectful.Outcome.cont, Outcome.halt,
    Locals.Source.Effectful.Outcome.halt]

/--
Inversion for a canonical regular loop execution.

The four alternatives are exactly the regular-producing branches of
`runForLoop`: false condition, body break, regular body/post recursion, and
continuing body/post recursion.
-/
theorem runForLoop_regular_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source final : σ}
    (hRun :
      Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel source =
        .ok (Outcome.regular final)) :
    ∃ stepFuel, fuel = stepFuel + 1 ∧
      ((∃ afterCond,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, false) ∧
            final = model.restrictTo loopCtx.scope afterCond) ∨
        (∃ afterCond afterBody,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.brk afterBody) ∧
            final = afterBody) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.regular afterBody) ∧
            Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok (Outcome.regular final)) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.cont afterBody) ∧
            Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok (Outcome.regular final))) := by
  cases fuel with
  | zero =>
      simp [Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
  | succ stepFuel =>
      refine ⟨stepFuel, rfl, ?_⟩
      rw [Stmt.runForLoop] at hRun
      cases hCond :
          Expr.evalCondition model prim cond source with
      | error err =>
          simp [hCond] at hRun
      | ok condResult =>
          rcases condResult with ⟨afterCond, condTrue⟩
          cases condTrue with
          | false =>
              left
              refine ⟨afterCond, rfl, ?_⟩
              simpa [hCond, Outcome.regular,
                Locals.Source.Effectful.Outcome.regular] using hRun.symm
          | true =>
              cases hBody :
                  Block.runScoped model prim program bodyBase body stepFuel
                    afterCond with
              | error err =>
                  simp [hCond, hBody] at hRun
              | ok bodyOutcome =>
                  rcases bodyOutcome with ⟨afterBody, bodyMode⟩
                  cases bodyMode with
                  | regular =>
                      cases hPost :
                          Block.runScoped model prim program postBase post
                            stepFuel afterBody with
                      | error err =>
                          simp [hCond, hBody, hPost] at hRun
                      | ok postOutcome =>
                          rcases postOutcome with ⟨afterPost, postMode⟩
                          cases postMode with
                          | regular =>
                              simp [hCond, hBody, hPost] at hRun
                              right
                              right
                              left
                              exact
                                ⟨afterCond, afterBody, afterPost,
                                  rfl, hBody, hPost, hRun⟩
                          | brk =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | cont =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | leave =>
                              simp [hCond, hBody, hPost] at hRun
                              have hMode :=
                                congrArg
                                  Locals.Source.Effectful.Outcome.mode hRun
                              simp [Outcome.regular,
                                Locals.Source.Effectful.Outcome.regular]
                                at hMode
                          | halt kind =>
                              simp [hCond, hBody, hPost] at hRun
                              have hMode :=
                                congrArg
                                  Locals.Source.Effectful.Outcome.mode hRun
                              simp [Outcome.regular,
                                Locals.Source.Effectful.Outcome.regular]
                                at hMode
                  | brk =>
                      right
                      left
                      refine ⟨afterCond, afterBody, rfl, hBody, ?_⟩
                      simpa [hCond, hBody, Outcome.regular,
                        Locals.Source.Effectful.Outcome.regular,
                        Outcome.brk,
                        Locals.Source.Effectful.Outcome.brk] using hRun.symm
                  | cont =>
                      cases hPost :
                          Block.runScoped model prim program postBase post
                            stepFuel afterBody with
                      | error err =>
                          simp [hCond, hBody, hPost] at hRun
                      | ok postOutcome =>
                          rcases postOutcome with ⟨afterPost, postMode⟩
                          cases postMode with
                          | regular =>
                              simp [hCond, hBody, hPost] at hRun
                              right
                              right
                              right
                              exact
                                ⟨afterCond, afterBody, afterPost,
                                  rfl, hBody, hPost, hRun⟩
                          | brk =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | cont =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | leave =>
                              simp [hCond, hBody, hPost] at hRun
                              have hMode :=
                                congrArg
                                  Locals.Source.Effectful.Outcome.mode hRun
                              simp [Outcome.regular,
                                Locals.Source.Effectful.Outcome.regular]
                                at hMode
                          | halt kind =>
                              simp [hCond, hBody, hPost] at hRun
                              have hMode :=
                                congrArg
                                  Locals.Source.Effectful.Outcome.mode hRun
                              simp [Outcome.regular,
                                Locals.Source.Effectful.Outcome.regular]
                                at hMode
                  | leave =>
                      simp [hCond, hBody] at hRun
                      have hMode :=
                        congrArg Locals.Source.Effectful.Outcome.mode hRun
                      simp [Outcome.regular,
                        Locals.Source.Effectful.Outcome.regular] at hMode
                  | halt kind =>
                      simp [hCond, hBody] at hRun
                      have hMode :=
                        congrArg Locals.Source.Effectful.Outcome.mode hRun
                      simp [Outcome.regular,
                        Locals.Source.Effectful.Outcome.regular] at hMode

/--
Inversion for a canonical loop execution that exits the current activation.

An exit is produced either directly by the body or post, or by a strictly
smaller recursive loop after a regular post. The theorem is mode-generic over
`leave` and terminal halts.
-/
theorem runForLoop_exit_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hExit : outcome.IsExit)
    (hRun :
      Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel source =
        .ok outcome) :
    ∃ stepFuel, fuel = stepFuel + 1 ∧
      ((∃ afterCond,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok outcome) ∨
        (∃ afterCond afterBody,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.regular afterBody) ∧
            Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok outcome) ∨
        (∃ afterCond afterBody,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.cont afterBody) ∧
            Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok outcome) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.regular afterBody) ∧
            Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok outcome) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.cont afterBody) ∧
            Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok outcome)) := by
  cases fuel with
  | zero =>
      simp [Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
  | succ stepFuel =>
      refine ⟨stepFuel, rfl, ?_⟩
      rw [Stmt.runForLoop] at hRun
      cases hCond :
          Expr.evalCondition model prim cond source with
      | error err =>
          simp [hCond] at hRun
      | ok condResult =>
          rcases condResult with ⟨afterCond, condTrue⟩
          cases condTrue with
          | false =>
              simp [hCond] at hRun
              subst outcome
              simp [Outcome.IsExit, Outcome.regular,
                Locals.Source.Effectful.Outcome.regular] at hExit
          | true =>
              cases hBody :
                  Block.runScoped model prim program bodyBase body stepFuel
                    afterCond with
              | error err =>
                  simp [hCond, hBody] at hRun
              | ok bodyOutcome =>
                  rcases bodyOutcome with ⟨afterBody, bodyMode⟩
                  cases bodyMode with
                  | regular =>
                      cases hPost :
                          Block.runScoped model prim program postBase post
                            stepFuel afterBody with
                      | error err =>
                          simp [hCond, hBody, hPost] at hRun
                      | ok postOutcome =>
                          rcases postOutcome with ⟨afterPost, postMode⟩
                          cases postMode with
                          | regular =>
                              simp [hCond, hBody, hPost] at hRun
                              right
                              right
                              right
                              left
                              exact
                                ⟨afterCond, afterBody, afterPost,
                                  rfl, hBody, hPost, hRun⟩
                          | brk =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | cont =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | leave =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              right
                              left
                              exact
                                ⟨afterCond, afterBody, rfl, hBody, hPost⟩
                          | halt kind =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              right
                              left
                              exact
                                ⟨afterCond, afterBody, rfl, hBody, hPost⟩
                  | brk =>
                      simp [hCond, hBody] at hRun
                      subst outcome
                      simp [Outcome.IsExit, Outcome.regular,
                        Locals.Source.Effectful.Outcome.regular] at hExit
                  | cont =>
                      cases hPost :
                          Block.runScoped model prim program postBase post
                            stepFuel afterBody with
                      | error err =>
                          simp [hCond, hBody, hPost] at hRun
                      | ok postOutcome =>
                          rcases postOutcome with ⟨afterPost, postMode⟩
                          cases postMode with
                          | regular =>
                              simp [hCond, hBody, hPost] at hRun
                              right
                              right
                              right
                              right
                              exact
                                ⟨afterCond, afterBody, afterPost,
                                  rfl, hBody, hPost, hRun⟩
                          | brk =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | cont =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | leave =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              right
                              right
                              left
                              exact
                                ⟨afterCond, afterBody, rfl, hBody, hPost⟩
                          | halt kind =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              right
                              right
                              left
                              exact
                                ⟨afterCond, afterBody, rfl, hBody, hPost⟩
                  | leave =>
                      simp [hCond, hBody] at hRun
                      subst outcome
                      left
                      exact ⟨afterCond, rfl, hBody⟩
                  | halt kind =>
                      simp [hCond, hBody] at hRun
                      subst outcome
                      left
                      exact ⟨afterCond, rfl, hBody⟩

/--
Canonical source `for` execution whose initializer is regular and whose first
body execution breaks.
-/
theorem run_for_body_brk_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source afterInit afterCond afterBody : σ}
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          (fuel + 1) init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hCond :
      Expr.evalCondition model prim cond afterInit =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterCond =
        .ok (Outcome.brk afterBody)) :
    Stmt.run model prim program ctx (fuel + 2)
        (.for_ init cond post body) source =
      .ok
        (Outcome.regular (model.restrictTo ctx.scope afterBody),
          ctx) := by
  simp [Stmt.run, hInit, Stmt.runForLoop, hCond, hBody,
    Outcome.regular, Locals.Source.Effectful.Outcome.regular,
    Outcome.brk, Locals.Source.Effectful.Outcome.brk]

/--
Canonical source `for` execution from a regular initializer and regular loop
result.
-/
theorem run_for_regular_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source afterInit final : σ}
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok (Outcome.regular final)) :
    Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok
        (Outcome.regular (model.restrictTo ctx.scope final),
          ctx) := by
  simp [Stmt.run, hInit, hLoop, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Canonical source `for` execution from a regular initializer and a leaving
loop result.
-/
theorem run_for_leave_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source afterInit final : σ}
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok (Outcome.leave final)) :
    Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok (Outcome.leave final, ctx) := by
  simp [Stmt.run, hInit, hLoop, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular, Outcome.leave,
    Locals.Source.Effectful.Outcome.leave]

/--
Canonical source `for` execution from a regular initializer and a halting loop
result.
-/
theorem run_for_halt_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source afterInit final : σ}
    {kind : Assembly.HaltKind}
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok (Outcome.halt kind final)) :
    Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok (Outcome.halt kind final, ctx) := by
  simp [Stmt.run, hInit, hLoop, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular, Outcome.halt,
    Locals.Source.Effectful.Outcome.halt]

/--
Canonical source `for` execution when a regular initializer is followed by an
activation-exiting loop outcome.
-/
theorem run_for_exit_of_runs {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source afterInit : σ} {outcome : Outcome σ}
    (hExit : outcome.IsExit)
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok outcome) :
    Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok (outcome, ctx) := by
  rcases outcome with ⟨final, outcomeMode⟩
  cases outcomeMode with
  | regular =>
      simp [Outcome.IsExit, Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hExit
  | brk =>
      simp [Outcome.IsExit, Outcome.brk,
        Locals.Source.Effectful.Outcome.brk] at hExit
  | cont =>
      simp [Outcome.IsExit, Outcome.cont,
        Locals.Source.Effectful.Outcome.cont] at hExit
  | leave =>
      exact run_for_leave_of_runs model prim program hInit hLoop
  | halt kind =>
      exact run_for_halt_of_runs model prim program hInit hLoop

/--
Canonical source `for` execution when its initializer exits the activation.
-/
theorem run_for_init_exit_of_runOpen {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx initCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hExit : outcome.IsExit)
    (hInit :
      Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (outcome, initCtx)) :
    Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok (outcome, ctx) := by
  rcases outcome with ⟨final, outcomeMode⟩
  cases outcomeMode with
  | regular =>
      simp [Outcome.IsExit, Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hExit
  | brk =>
      simp [Outcome.IsExit, Outcome.brk,
        Locals.Source.Effectful.Outcome.brk] at hExit
  | cont =>
      simp [Outcome.IsExit, Outcome.cont,
        Locals.Source.Effectful.Outcome.cont] at hExit
  | leave =>
      rw [Stmt.run, hInit]
      rfl
  | halt kind =>
      rw [Stmt.run, hInit]
      rfl

/--
Canonical source `if` execution when the condition is false.
-/
theorem run_if_false_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {source afterCond : σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, false)) :
    Stmt.run model prim program ctx (fuel + 1)
        (.if_ cond body) source =
      .ok (Outcome.regular afterCond, ctx) := by
  simp [Stmt.run, hCond, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Canonical source `if` execution when the condition is true.
-/
theorem run_if_true_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {source afterCond : σ} {outcome : Outcome σ}
    (hCond :
      Expr.evalCondition model prim cond source =
        .ok (afterCond, true))
    (hBody :
      Block.runScoped model prim program ctx body fuel afterCond =
        .ok outcome) :
    Stmt.run model prim program ctx (fuel + 1)
        (.if_ cond body) source =
      .ok (outcome, ctx) := by
  simp [Stmt.run, hCond, hBody]

/--
Canonical source `switch` execution when no case or default is selected.
-/
theorem run_switch_none_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {source afterScrutinee : σ} {value : Word}
    (hScrutinee :
      Expr.evalOne model prim scrutinee source =
        .ok (afterScrutinee, value))
    (hSelect :
      Source.Switch.select value cases defaultBody = none) :
    Stmt.run model prim program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) source =
      .ok (Outcome.regular afterScrutinee, ctx) := by
  simp [Stmt.run, hScrutinee, hSelect]

/--
Canonical source `switch` execution when a case or default body is selected.
-/
theorem run_switch_some_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {selected : Functions.Block}
    {source afterScrutinee : σ} {value : Word}
    {outcome : Outcome σ}
    (hScrutinee :
      Expr.evalOne model prim scrutinee source =
        .ok (afterScrutinee, value))
    (hSelect :
      Source.Switch.select value cases defaultBody = some selected)
    (hBody :
      Block.runScoped model prim program ctx selected fuel
          afterScrutinee =
        .ok outcome) :
    Stmt.run model prim program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) source =
      .ok (outcome, ctx) := by
  simp [Stmt.run, hScrutinee, hSelect, hBody]

end Stmt

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpen_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Source.Ctx} {block : Block}
        {state : σ} {outcome : Outcome σ} {runCtx : Source.Ctx},
        fuel ≤ fuel' →
        Block.runOpen model prim program ctx fuel block state =
          .ok (outcome, runCtx) →
        Block.runOpen model prim program ctx fuel' block state =
          .ok (outcome, runCtx) := by
    intro fuel fuel' ctx block state outcome runCtx hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpen, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            cases block with
            | mk stmts =>
                cases stmts with
                | nil =>
                    simpa [Block.runOpen] using hRun
                | cons stmt rest =>
                    cases hStmt :
                        Stmt.run model prim program ctx fuel stmt state with
                    | error err =>
                        simp [Block.runOpen, hStmt] at hRun
                    | ok stmtResult =>
                        rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                        have hStmt' :
                            Stmt.run model prim program ctx fuel' stmt state =
                              .ok (stmtOutcome, stmtCtx) :=
                          Stmt.run_mono model prim program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact
                              Block.runOpen_mono model prim program
                                hFuelLe hRun
                        | brk =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
  termination_by
    fuel _fuel' _ctx block _state _outcome _runCtx _hLe _hRun =>
      (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Source.Ctx} {block : Block}
        {state : σ} {outcome : Outcome σ},
        fuel ≤ fuel' →
        Block.runScoped model prim program ctx block fuel state =
          .ok outcome →
        Block.runScoped model prim program ctx block fuel' state =
          .ok outcome := by
    intro fuel fuel' ctx block state outcome hLe hRun
    unfold Block.runScoped at hRun ⊢
    cases hOpen :
        Block.runOpen model prim program ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        have hOpen' :
            Block.runOpen model prim program ctx fuel' block state =
              .ok (openOutcome, finalCtx) :=
          Block.runOpen_mono model prim program hLe hOpen
        cases hMode : openOutcome.mode with
        | regular =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | brk =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | cont =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | leave =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | halt kind =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
  termination_by
    fuel _fuel' _ctx block _state _outcome _hLe _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem FunDef.runBody_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {fn : FunDef} {args : List Word}
        {state : σ} {result : CallResult σ},
        fuel ≤ fuel' →
        FunDef.runBody model prim program fn args fuel state = .ok result →
        FunDef.runBody model prim program fn args fuel' state = .ok result := by
    intro fuel fuel' fn args state result hLe hRun
    cases fuel with
    | zero =>
        simp [FunDef.runBody, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            cases hParams :
                Source.Store.insertMany fn.params args
                  Locals.Source.Store.empty with
            | none =>
                simp [FunDef.runBody, hParams, Source.invalid,
                  Structured.invalid] at hRun
            | some paramStore =>
                let initialStore :=
                  Source.Store.initReturns fn.returns paramStore
                let callerSource := model.source state
                let initialSource : Locals.Source.State :=
                  { shared := callerSource.shared, vars := initialStore }
                let initialState := model.withSource state initialSource
                let functionScope := fn.returns ++ fn.params
                let bodyCtx :=
                  { Source.Ctx.initial.withLeaveScope functionScope with
                    scope := functionScope }
                cases hBody :
                    Block.runOpen model prim program bodyCtx fuel fn.body
                      initialState with
                | error err =>
                    simp [FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with ⟨bodyOutcome, bodyFinalCtx⟩
                    have hBody' :
                        Block.runOpen model prim program bodyCtx fuel' fn.body
                            initialState =
                          .ok (bodyOutcome, bodyFinalCtx) :=
                      Block.runOpen_mono model prim program hFuelLe hBody
                    cases hMode : bodyOutcome.mode with
                    | regular =>
                        simp [FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
                    | brk =>
                        simp [FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode,
                          Source.invalid, Structured.invalid] at hRun
                    | cont =>
                        simp [FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode,
                          Source.invalid, Structured.invalid] at hRun
                    | leave =>
                        simp [FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
  termination_by
    fuel _fuel' fn _args _state _result _hLe _hRun =>
      (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {loopCtx : Source.Ctx}
        {cond : Expr 1} {postBase : Source.Ctx} {post : Block}
        {bodyBase : Source.Ctx} {body : Block} {state : σ}
        {outcome : Outcome σ},
        fuel ≤ fuel' →
        Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel state = .ok outcome →
        Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel' state = .ok outcome := by
    intro fuel fuel' loopCtx cond postBase post bodyBase body state outcome
      hLe hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Stmt.runForLoop at hRun ⊢
            cases hCond : Expr.evalCondition model prim cond state with
            | error err =>
                simp [hCond] at hRun ⊢
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                cases condTrue with
                | false =>
                    simp [hCond] at hRun ⊢
                    exact hRun
                | true =>
                    simp [hCond] at hRun ⊢
                    cases hBody :
                        Block.runScoped model prim program bodyBase body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Block.runScoped model prim program bodyBase body
                              fuel' stateAfterCond = .ok bodyOutcome :=
                          Block.runScoped_mono model prim program
                            hFuelLe hBody
                        cases hBodyMode : bodyOutcome.mode with
                        | brk =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | regular =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScoped model prim program postBase
                                  post fuel bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped model prim program
                                        postBase post fuel'
                                        bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.runScoped_mono model prim program
                                    hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono model prim program
                                        hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | cont =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScoped model prim program postBase
                                  post fuel bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped model prim program
                                        postBase post fuel'
                                        bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.runScoped_mono model prim program
                                    hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono model prim program
                                        hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | leave =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
  termination_by
    fuel _fuel' _loopCtx _cond _postBase _post _bodyBase _body _state
      _outcome _hLe _hRun => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Source.Ctx} {stmt : Stmt} {state : σ}
        {outcome : Outcome σ} {runCtx : Source.Ctx},
        fuel ≤ fuel' →
        Stmt.run model prim program ctx fuel stmt state =
          .ok (outcome, runCtx) →
        Stmt.run model prim program ctx fuel' stmt state =
          .ok (outcome, runCtx) := by
    intro fuel fuel' ctx stmt state outcome runCtx hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Stmt.run] using hRun
    | let_ name value =>
        simpa [Stmt.run] using hRun
    | assign name value =>
        simpa [Stmt.run] using hRun
    | block body =>
        unfold Stmt.run at hRun ⊢
        cases hBody :
            Block.runScoped model prim program ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            have hBody' :
                Block.runScoped model prim program ctx body fuel' state =
                  .ok bodyOutcome :=
              Block.runScoped_mono model prim program hLe hBody
            simp [hBody, hBody'] at hRun ⊢
            exact hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hCond :
                    Expr.evalCondition model prim cond state with
                | error err =>
                    simp [hCond] at hRun ⊢
                | ok condResult =>
                    rcases condResult with ⟨stateAfterCond, condTrue⟩
                    cases condTrue with
                    | false =>
                        simp [hCond] at hRun ⊢
                        exact hRun
                    | true =>
                        simp [hCond] at hRun ⊢
                        cases hBody :
                            Block.runScoped model prim program ctx body fuel
                              stateAfterCond with
                        | error err =>
                            simp [hBody] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped model prim program ctx body
                                    fuel' stateAfterCond =
                                  .ok bodyOutcome :=
                              Block.runScoped_mono model prim program
                                hFuelLe hBody
                            simp [hBody, hBody'] at hRun ⊢
                            exact hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hScrutinee :
                    Expr.evalOne model prim scrutinee state with
                | error err =>
                    simp [hScrutinee] at hRun ⊢
                | ok scrutineeResult =>
                    rcases scrutineeResult with ⟨stateAfterScrutinee, value⟩
                    cases hSelected :
                        Source.Switch.select value cases defaultBody with
                    | none =>
                        simp [hScrutinee, hSelected] at hRun ⊢
                        exact hRun
                    | some selected =>
                        simp [hScrutinee, hSelected] at hRun ⊢
                        cases hBody :
                            Block.runScoped model prim program ctx selected
                              fuel stateAfterScrutinee with
                        | error err =>
                            simpa [hBody] using hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped model prim program ctx selected
                                    fuel' stateAfterScrutinee =
                                  .ok bodyOutcome :=
                              Block.runScoped_mono model prim program
                                hFuelLe hBody
                            simpa [hBody, hBody'] using hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                let initBase := ctx.withoutLoopControl
                cases hInit :
                    Block.runOpen model prim program initBase fuel init state
                with
                | error err =>
                    simp [initBase, hInit] at hRun
                | ok initResult =>
                    rcases initResult with ⟨initOutcome, initCtx⟩
                    have hInit' :
                        Block.runOpen model prim program initBase fuel' init
                            state =
                          .ok (initOutcome, initCtx) :=
                      Block.runOpen_mono model prim program hFuelLe hInit
                    cases hInitMode : initOutcome.mode with
                    | regular =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        let loopCtx := initCtx
                        let postBase := initCtx.withoutLoopControl
                        let bodyBase :=
                          initCtx.withLoopControl initCtx.scope initCtx.scope
                        cases hLoop :
                            Stmt.runForLoop model prim program loopCtx cond
                              postBase post bodyBase body fuel
                              initOutcome.state with
                        | error err =>
                            simp [loopCtx, postBase, bodyBase, hLoop] at hRun
                        | ok loopOutcome =>
                            have hLoop' :
                                Stmt.runForLoop model prim program loopCtx cond
                                    postBase post bodyBase body fuel'
                                    initOutcome.state =
                                  .ok loopOutcome :=
                              Stmt.runForLoop_mono model prim program
                                hFuelLe hLoop
                            cases hLoopMode : loopOutcome.mode with
                            | regular =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode] at hRun ⊢
                                exact hRun
                            | brk =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode, Source.invalid,
                                  Structured.invalid] at hRun
                            | cont =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode, Source.invalid,
                                  Structured.invalid] at hRun
                            | leave =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode] at hRun ⊢
                                exact hRun
                            | halt kind =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode] at hRun ⊢
                                exact hRun
                    | brk =>
                        simp [initBase, hInit, hInit', hInitMode,
                          Source.invalid, Structured.invalid] at hRun
                    | cont =>
                        simp [initBase, hInit, hInit', hInitMode,
                          Source.invalid, Structured.invalid] at hRun
                    | leave =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
    | brk =>
        simpa [Stmt.run] using hRun
    | cont =>
        simpa [Stmt.run] using hRun
    | leave =>
        simpa [Stmt.run] using hRun
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                by_cases hTargets : targets.Nodup
                · simp [hTargets] at hRun ⊢
                  cases hArgs :
                      ArgList.eval model prim args state with
                  | error err =>
                      simp [hArgs] at hRun ⊢
                  | ok argResult =>
                      rcases argResult with ⟨stateAfterArgs, argValues⟩
                      cases hLookup :
                          Source.FunList.find? functionName
                            program.functions with
                      | none =>
                          simp [hArgs, hLookup, Source.invalid,
                            Structured.invalid] at hRun
                      | some fn =>
                          cases hBody :
                              FunDef.runBody model prim program fn argValues
                                fuel stateAfterArgs with
                          | error err =>
                              simp [hArgs, hLookup, hBody] at hRun
                          | ok callResult =>
                              have hBody' :
                                  FunDef.runBody model prim program fn
                                      argValues fuel' stateAfterArgs =
                                    .ok callResult :=
                                FunDef.runBody_mono model prim program
                                  hFuelLe hBody
                              cases callResult with
                              | returned stateAfterCall returnValues =>
                                  simp [hArgs, hLookup, hBody, hBody']
                                    at hRun ⊢
                                  exact hRun
                              | halted kind haltedState =>
                                  simp [hArgs, hLookup, hBody, hBody']
                                    at hRun ⊢
                                  exact hRun
                · simp [hTargets, Source.invalid, Structured.invalid] at hRun
    | terminal kind =>
        simpa [Stmt.run] using hRun
    | terminalArgs kind args =>
        simpa [Stmt.run] using hRun
  termination_by
    fuel _fuel' _ctx stmt _state _outcome _runCtx _hLe _hRun =>
      (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Block

/--
A regular open-block result becomes a scoped result by restricting only the
source variable store to the incoming lexical scope.
-/
theorem runScoped_regular_of_runOpen {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {block : Block} {source final : σ}
    (hOpen :
      Block.runOpen model prim program ctx fuel block source =
        .ok (Outcome.regular final, finalCtx)) :
    Block.runScoped model prim program ctx block fuel source =
      .ok (Outcome.regular (model.restrictTo ctx.scope final)) := by
  simp [Block.runScoped, hOpen, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Abrupt open-block outcomes pass through scoped execution unchanged.
-/
theorem runScoped_nonregular_of_runOpen {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {block : Block} {source : σ} {outcome : Outcome σ}
    (hOpen :
      Block.runOpen model prim program ctx fuel block source =
        .ok (outcome, finalCtx))
    (hMode : outcome.mode ≠ .regular) :
    Block.runScoped model prim program ctx block fuel source =
      .ok outcome := by
  cases hOutcome : outcome.mode with
  | regular =>
      exact False.elim (hMode hOutcome)
  | brk =>
      simp [Block.runScoped, hOpen, hOutcome]
  | cont =>
      simp [Block.runScoped, hOpen, hOutcome]
  | leave =>
      simp [Block.runScoped, hOpen, hOutcome]
  | halt kind =>
      simp [Block.runScoped, hOpen, hOutcome]

/--
Compose one successful regular source statement with a reconstructed tail at
a common canonical Functions fuel.
-/
theorem runOpen_cons_regular_exists {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {headFuel tailFuel : Nat} {ctx midCtx finalCtx : Source.Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {source mid : σ} {outcome : Outcome σ}
    (hHead :
      Stmt.run model prim program ctx headFuel stmt source =
        .ok (Outcome.regular mid, midCtx))
    (hTail :
      Block.runOpen model prim program midCtx tailFuel
          { stmts := rest } mid =
        .ok (outcome, finalCtx)) :
    ∃ fuel,
      Block.runOpen model prim program ctx fuel
          { stmts := stmt :: rest } source =
        .ok (outcome, finalCtx) := by
  let commonFuel := Nat.max headFuel tailFuel
  have hHead' :
      Stmt.run model prim program ctx commonFuel stmt source =
        .ok (Outcome.regular mid, midCtx) :=
    Stmt.run_mono model prim program (Nat.le_max_left _ _) hHead
  have hTail' :
      Block.runOpen model prim program midCtx commonFuel
          { stmts := rest } mid =
        .ok (outcome, finalCtx) :=
    Block.runOpen_mono model prim program (Nat.le_max_right _ _) hTail
  exact
    ⟨commonFuel + 1,
      by simp [Block.runOpen, hHead', hTail',
        Outcome.regular, Locals.Source.Effectful.Outcome.regular]⟩

/--
A nonregular source statement makes the remaining source list unreachable.
-/
theorem runOpen_cons_nonregular {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {fuel : Nat} {ctx stmtCtx : Source.Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {source : σ} {outcome : Outcome σ}
    (hHead :
      Stmt.run model prim program ctx fuel stmt source =
        .ok (outcome, stmtCtx))
    (hMode : outcome.mode ≠ .regular) :
    Block.runOpen model prim program ctx (fuel + 1)
        { stmts := stmt :: rest } source =
      .ok (outcome, ctx) := by
  cases hOutcomeMode : outcome.mode with
  | regular =>
      exact False.elim (hMode hOutcomeMode)
  | brk =>
      simp [Block.runOpen, hHead, hOutcomeMode]
  | cont =>
      simp [Block.runOpen, hHead, hOutcomeMode]
  | leave =>
      simp [Block.runOpen, hHead, hOutcomeMode]
  | halt kind =>
      simp [Block.runOpen, hHead, hOutcomeMode]

end Block

namespace Program

def runState {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (program : Functions.Program) (state : σ) :
    Except EVMException (Outcome σ) :=
  Block.runScoped model prim program Source.Ctx.initial
    program.body fuel state

end Program

end Effectful

/-!
Canonical Functions semantics.

New compiler-pass preservation and effect specializations use this
parameterized interpreter. `Functions.SourceSemantics` remains available as a
compatibility semantics for existing non-effect proofs, but it is not the
semantic authority for observer-aware boundaries.
-/
namespace Canonical

abbrev StateModel := Effectful.StateModel
abbrev PrimitiveSemantics := Effectful.PrimitiveSemantics
abbrev Outcome := Effectful.Outcome

namespace Program

abbrev runState {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (program : Functions.Program) (state : σ) :
    Except EVMException (Outcome σ) :=
  Effectful.Program.runState model prim fuel program state

end Program

end Canonical
end Source
end Functions
end EvmCompiler
