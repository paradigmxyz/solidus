import EvmCompiler.Locals.SourceSemantics

namespace EvmCompiler
namespace Locals
namespace Source
namespace Effectful

/-!
Reusable effect-carrying semantics for the stack-free locals language.

`SourceSemantics` remains the ordinary public interpreter. This module factors
the control-flow interpreter over a small state projection and an effectful
primitive handler, so observers and future external effects do not need to
copy the locals evaluator.
-/

structure StateModel (σ : Type) where
  source : σ → Source.State
  withSource : σ → Source.State → σ

class SourceView (σ : Type) where
  source : σ → Source.State

namespace StateModel

def shared {σ : Type} (model : StateModel σ) (state : σ) :
    EvmYul.SharedState .EVM :=
  (model.source state).shared

def vars {σ : Type} (model : StateModel σ) (state : σ) : Source.Store :=
  (model.source state).vars

def withShared {σ : Type} (model : StateModel σ) (state : σ)
    (shared : EvmYul.SharedState .EVM) : σ :=
  model.withSource state ((model.source state).withShared shared)

def withVars {σ : Type} (model : StateModel σ) (state : σ)
    (vars : Source.Store) : σ :=
  model.withSource state ((model.source state).withVars vars)

def restrictTo {σ : Type} (model : StateModel σ) (scope : List Name)
    (state : σ) : σ :=
  model.withSource state ((model.source state).restrictTo scope)

def insert {σ : Type} (model : StateModel σ) (state : σ) (name : Name)
    (value : Word) : σ :=
  model.withSource state ((model.source state).insert name value)

end StateModel

structure PrimitiveSemantics (σ : Type) where
  eval :
    Structured.BasicOp → σ → List Word →
      Except EVMException (σ × List Word)
  terminal :
    Assembly.HaltKind → σ → List Word → Except EVMException σ

namespace PrimitiveSemantics

/--
Every successful effect produced by `source` is reproduced exactly by
`target`. This is the semantic interface used to specialize the canonical
parameterized interpreter with additional dynamic guards without duplicating
its control flow.
-/
def SuccessRefines {σ : Type}
    (source target : PrimitiveSemantics σ) : Prop :=
  (∀ op state values final outputs,
      source.eval op state values = .ok (final, outputs) →
        target.eval op state values = .ok (final, outputs)) ∧
    ∀ kind state values final,
      source.terminal kind state values = .ok final →
        target.terminal kind state values = .ok final

theorem SuccessRefines.eval
    {σ : Type} {source target : PrimitiveSemantics σ}
    (hRefines : SuccessRefines source target)
    {op : Structured.BasicOp} {state final : σ}
    {values outputs : List Word}
    (hEval : source.eval op state values = .ok (final, outputs)) :
    target.eval op state values = .ok (final, outputs) :=
  hRefines.1 op state values final outputs hEval

theorem SuccessRefines.terminal
    {σ : Type} {source target : PrimitiveSemantics σ}
    (hRefines : SuccessRefines source target)
    {kind : Assembly.HaltKind} {state final : σ}
    {values : List Word}
    (hEval : source.terminal kind state values = .ok final) :
    target.terminal kind state values = .ok final :=
  hRefines.2 kind state values final hEval

theorem SuccessRefines.refl {σ : Type}
    (prim : PrimitiveSemantics σ) :
    SuccessRefines prim prim := by
  exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem SuccessRefines.trans
    {σ : Type} {first second third : PrimitiveSemantics σ}
    (hFirst : SuccessRefines first second)
    (hSecond : SuccessRefines second third) :
    SuccessRefines first third := by
  constructor
  · intro op state values final outputs hEval
    exact hSecond.eval (hFirst.eval hEval)
  · intro kind state values final hEval
    exact hSecond.terminal (hFirst.terminal hEval)

end PrimitiveSemantics

namespace Ordinary

def stateModel : StateModel Source.State where
  source := id
  withSource := fun _state source => source

def primitiveSemantics
    (prim : Source.PrimitiveSemantics) :
    PrimitiveSemantics Source.State where
  eval op state values := do
    let (shared, values') ← prim.eval op state.shared values
    .ok (state.withShared shared, values')
  terminal kind state values := do
    let shared ← prim.terminal kind state.shared values
    .ok (state.withShared shared)

end Ordinary

structure Outcome (σ : Type) where
  state : σ
  mode : Source.Mode

namespace Outcome

def regular {σ : Type} (state : σ) : Outcome σ :=
  { state := state, mode := .regular }

def brk {σ : Type} (state : σ) : Outcome σ :=
  { state := state, mode := .brk }

def cont {σ : Type} (state : σ) : Outcome σ :=
  { state := state, mode := .cont }

def leave {σ : Type} (state : σ) : Outcome σ :=
  { state := state, mode := .leave }

def halt {σ : Type} (kind : Assembly.HaltKind) (state : σ) : Outcome σ :=
  { state := state, mode := .halt kind }

def toSource {σ : Type} [SourceView σ] (outcome : Outcome σ) :
    Source.Outcome :=
  { state := SourceView.source outcome.state, mode := outcome.mode }

end Outcome

namespace Expr

mutual
  def eval {σ : Type} {results : Nat} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (expr : Locals.Expr results)
      (state : σ) : Except EVMException (σ × List Word) :=
    match expr with
    | .lit value =>
        .ok (state, [value])
    | .var name =>
        match model.vars state name with
        | some value => .ok (state, [value])
        | none => Source.invalid
    | .code _code =>
        Source.invalid
    | .prim op args => do
        let (stateAfterArgs, values) ←
          ExprSeq.eval model prim args state
        prim.eval op stateAfterArgs values

  def ExprSeq.eval {σ : Type} {results : Nat}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (exprs : Locals.ExprSeq results) (state : σ) :
      Except EVMException (σ × List Word) :=
    match exprs with
    | .nil => .ok (state, [])
    | .cons head tail => do
        let (stateAfterHead, headValues) ← eval model prim head state
        let (stateAfterTail, tailValues) ←
          ExprSeq.eval model prim tail stateAfterHead
        .ok (stateAfterTail, headValues ++ tailValues)
end

mutual
  /--
  Expression evaluation is monotone under successful primitive refinement.
  -/
  theorem eval_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      {results : Nat} {expr : Locals.Expr results}
      {source final : σ} {values : List Word}
      (hEval :
        eval model sourcePrim expr source = .ok (final, values)) :
      eval model targetPrim expr source = .ok (final, values) := by
    cases expr with
    | lit value =>
        simpa [eval] using hEval
    | var name =>
        simpa [eval] using hEval
    | code code =>
        simp [eval, Source.invalid, Structured.invalid] at hEval
    | prim op args =>
        simp only [eval] at hEval ⊢
        cases hArgs : ExprSeq.eval model sourcePrim args source with
        | error err =>
            simp [hArgs] at hEval
        | ok result =>
            rcases result with ⟨afterArgs, argValues⟩
            simp only [hArgs, Bind.bind, Except.bind] at hEval
            have hArgs' :
                ExprSeq.eval model targetPrim args source =
                  .ok (afterArgs, argValues) :=
              ExprSeq.eval_of_successRefines model hRefines hArgs
            rw [hArgs']
            exact hRefines.eval hEval

  theorem ExprSeq.eval_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      {results : Nat} {exprs : Locals.ExprSeq results}
      {source final : σ} {values : List Word}
      (hEval :
        ExprSeq.eval model sourcePrim exprs source =
          .ok (final, values)) :
      ExprSeq.eval model targetPrim exprs source =
        .ok (final, values) := by
    cases exprs with
    | nil =>
        simpa [ExprSeq.eval] using hEval
    | @cons left right head tail =>
        simp only [ExprSeq.eval] at hEval ⊢
        cases hHead : eval model sourcePrim head source with
        | error err =>
            simp [hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨afterHead, headValues⟩
            simp only [hHead, Bind.bind, Except.bind] at hEval
            cases hTail :
                ExprSeq.eval model sourcePrim tail afterHead with
            | error err =>
                simp [hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨tailFinal, tailValues⟩
                simp only [hTail, Bind.bind, Except.bind] at hEval
                have hHead' :
                    eval model targetPrim head source =
                      .ok (afterHead, headValues) :=
                  eval_of_successRefines model hRefines hHead
                have hTail' :
                    ExprSeq.eval model targetPrim tail afterHead =
                      .ok (tailFinal, tailValues) :=
                  ExprSeq.eval_of_successRefines model hRefines hTail
                simpa [hHead', hTail'] using hEval
end

def evalOne {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Locals.Expr results)
    (state : σ) : Except EVMException (σ × Word) := do
  let (state', values) ← eval model prim expr state
  match values with
  | [value] => .ok (state', value)
  | _ => Source.invalid

def evalCondition {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Locals.Expr 1)
    (state : σ) : Except EVMException (σ × Bool) := do
  let (state', value) ← evalOne model prim expr state
  .ok (state', value != EvmYul.UInt256.ofNat 0)

theorem evalOne_of_successRefines
    {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
    (model : StateModel σ)
    (hRefines : sourcePrim.SuccessRefines targetPrim)
    {results : Nat} {expr : Locals.Expr results}
    {source final : σ} {value : Word}
    (hEval :
      evalOne model sourcePrim expr source = .ok (final, value)) :
    evalOne model targetPrim expr source = .ok (final, value) := by
  unfold evalOne at hEval ⊢
  cases hExpr : eval model sourcePrim expr source with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨afterExpr, values⟩
      have hExpr' :
          eval model targetPrim expr source = .ok (afterExpr, values) :=
        eval_of_successRefines model hRefines hExpr
      simp only [hExpr, hExpr', Bind.bind, Except.bind] at hEval ⊢
      exact hEval

theorem evalCondition_of_successRefines
    {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
    (model : StateModel σ)
    (hRefines : sourcePrim.SuccessRefines targetPrim)
    {expr : Locals.Expr 1}
    {source final : σ} {condition : Bool}
    (hEval :
      evalCondition model sourcePrim expr source =
        .ok (final, condition)) :
    evalCondition model targetPrim expr source =
      .ok (final, condition) := by
  unfold evalCondition at hEval ⊢
  cases hExpr : evalOne model sourcePrim expr source with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨afterExpr, value⟩
      have hExpr' :
          evalOne model targetPrim expr source = .ok (afterExpr, value) :=
        evalOne_of_successRefines model hRefines hExpr
      simpa [hExpr, hExpr'] using hEval

end Expr

namespace Ordinary

mutual
  theorem expr_eval_eq_source {results : Nat}
      (prim : Source.PrimitiveSemantics)
      (expr : Locals.Expr results) (state : Source.State) :
      Effectful.Expr.eval stateModel (primitiveSemantics prim) expr state =
        Source.Expr.eval prim expr state := by
    cases expr with
    | lit value =>
        rfl
    | var name =>
        rfl
    | code code =>
        rfl
    | prim op args =>
        simp only [Effectful.Expr.eval, Source.Expr.eval]
        rw [exprSeq_eval_eq_source prim args state]
        rfl

  theorem exprSeq_eval_eq_source {results : Nat}
      (prim : Source.PrimitiveSemantics)
      (exprs : Locals.ExprSeq results) (state : Source.State) :
      Effectful.Expr.ExprSeq.eval
          stateModel (primitiveSemantics prim) exprs state =
        Source.Expr.ExprSeq.eval prim exprs state := by
    cases exprs with
    | nil =>
        rfl
    | cons head tail =>
        simp only [Effectful.Expr.ExprSeq.eval, Source.Expr.ExprSeq.eval]
        rw [expr_eval_eq_source prim head state]
        cases hHead : Source.Expr.eval prim head state with
        | error err =>
            rfl
        | ok result =>
            rcases result with ⟨stateAfterHead, values⟩
            change
              (do
                let (stateAfterTail, tailValues) ←
                  Effectful.Expr.ExprSeq.eval stateModel
                    (primitiveSemantics prim) tail stateAfterHead
                .ok (stateAfterTail, values ++ tailValues)) =
              (do
                let (stateAfterTail, tailValues) ←
                  Source.Expr.ExprSeq.eval prim tail stateAfterHead
                .ok (stateAfterTail, values ++ tailValues))
            rw [exprSeq_eval_eq_source prim tail stateAfterHead]
end

end Ordinary

mutual
  def Block.runOpen {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Locals.Program)
      (ctx : Source.Ctx) : Nat → Locals.Block → σ →
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
      (prim : PrimitiveSemantics σ) (program : Locals.Program)
      (ctx : Source.Ctx) (block : Locals.Block) (fuel : Nat)
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

  def Stmt.runForLoop {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Locals.Program)
      (loopCtx : Source.Ctx) (cond : Locals.Expr 1)
      (postBase : Source.Ctx) (post : Locals.Block)
      (bodyBase : Source.Ctx) (body : Locals.Block) :
      Nat → σ → Except EVMException (Outcome σ)
    | 0, _state =>
        Source.invalid
    | fuel + 1, state =>
        match Expr.evalCondition model prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.runScoped model prim program bodyBase body fuel
                  stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.runScoped model prim program postBase post
                          fuel bodyOutcome.state with
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
  termination_by fuel _state => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (program : Locals.Program)
      (ctx : Source.Ctx) :
      Nat → Locals.Stmt → σ →
        Except EVMException (Outcome σ × Source.Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ← Expr.eval model prim expr state
        .ok (Outcome.regular state', ctx)
    | _fuel, .exprs exprs, state => do
        let (state', _values) ← Expr.ExprSeq.eval model prim exprs state
        .ok (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ←
          Expr.evalOne model prim value state
        .ok
          (Outcome.regular (model.insert stateAfterValue name value'),
            { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if model.vars state |>.contains name then
          let (stateAfterValue, value') ←
            Expr.evalOne model prim value state
          .ok
            (Outcome.regular
              (model.withVars stateAfterValue
                (Source.Store.insert (model.vars stateAfterValue)
                  name value')),
              ctx)
        else
          Source.invalid
    | _fuel, .assignTop _name, _state =>
        Source.invalid
    | _fuel, .assignTopWithOffset _offset _name, _state =>
        Source.invalid
    | _fuel, .promoteName _name, _state =>
        Source.invalid
    | _fuel, .cleanupTo _targetLayout, _state =>
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
    | _fuel, .call _name, _state =>
        Source.invalid
    | _fuel, .terminal kind, state => do
        let state' ← prim.terminal kind state []
        .ok (Outcome.halt kind state', ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ←
          Expr.ExprSeq.eval model prim args state
        let state' ← prim.terminal kind stateAfterArgs values
        .ok (Outcome.halt kind state', ctx)
  termination_by fuel stmt _state => (fuel, 3, sizeOf stmt)
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
    (program : Locals.Program) (state : σ) :
    Except EVMException (Outcome σ) :=
  Block.runScoped model prim program Source.Ctx.initial
    program.body fuel state

inductive Eval {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) :
    Nat → Locals.Program → σ → Outcome σ → Prop where
  | ofRun {fuel : Nat} {program : Locals.Program} {initial : σ}
      {outcome : Outcome σ}
      (hRun : runState model prim fuel program initial = .ok outcome) :
      Eval model prim fuel program initial outcome

end Program

end Effectful
end Source
end Locals
end EvmCompiler
