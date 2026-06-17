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

theorem restrictTo_congr
    {σ : Type} (model : StateModel σ)
    {left right : List Name} {state : σ}
    (hScope : ∀ name, name ∈ left ↔ name ∈ right) :
    model.restrictTo left state = model.restrictTo right state := by
  unfold restrictTo
  rw [Source.State.restrictTo_congr hScope]

def insert {σ : Type} (model : StateModel σ) (state : σ) (name : Name)
    (value : Word) : σ :=
  model.withSource state ((model.source state).insert name value)

end StateModel

namespace Control

/--
The effect owner used by the monad-polymorphic Locals evaluator.

The handler owns complete primitive and terminal steps, allowing the same
expression and control recursion to serve ordinary execution, resource
observation, and open CALL/CREATE interaction.
-/
structure PrimitiveSemantics (M : Type → Type) (σ : Type) where
  eval :
    Structured.BasicOp → σ → List Word → M (σ × List Word)
  terminal :
    Assembly.HaltKind → σ → List Word → M σ

end Control

abbrev PrimitiveSemantics (σ : Type) :=
  Control.PrimitiveSemantics (Except EVMException) σ

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

namespace Control

mutual
  def eval {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} {results : Nat} (model : StateModel σ)
      (prim : Effectful.Control.PrimitiveSemantics M σ)
      (expr : Locals.Expr results) (state : σ) :
      M (σ × List Word) :=
    match expr with
    | .lit value =>
        pure (state, [value])
    | .var name =>
        match model.vars state name with
        | some value => pure (state, [value])
        | none => throw .InvalidInstruction
    | .code _code =>
        throw .InvalidInstruction
    | .prim op args => do
        let (stateAfterArgs, values) ←
          ExprSeq.eval model prim args state
        prim.eval op stateAfterArgs values

  def ExprSeq.eval {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} {results : Nat}
      (model : StateModel σ)
      (prim : Effectful.Control.PrimitiveSemantics M σ)
      (exprs : Locals.ExprSeq results) (state : σ) :
      M (σ × List Word) :=
    match exprs with
    | .nil => pure (state, [])
    | .cons head tail => do
        let (stateAfterHead, headValues) ← eval model prim head state
        let (stateAfterTail, tailValues) ←
          ExprSeq.eval model prim tail stateAfterHead
        pure (stateAfterTail, headValues ++ tailValues)
end

def evalOne {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : Effectful.Control.PrimitiveSemantics M σ)
    (expr : Locals.Expr results) (state : σ) : M (σ × Word) := do
  let (state', values) ← eval model prim expr state
  match values with
  | [value] => pure (state', value)
  | _ => throw .InvalidInstruction

def evalCondition {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : Effectful.Control.PrimitiveSemantics M σ)
    (expr : Locals.Expr 1) (state : σ) : M (σ × Bool) := do
  let (state', value) ← evalOne model prim expr state
  pure (state', value != EvmYul.UInt256.ofNat 0)

end Control

/-!
Keep the constructor equations of the canonical kernel available to adjacent
proof owners. Public wrappers may change representation without forcing every
consumer to know how many wrapper layers must be unfolded.
-/
attribute [simp] Control.eval Control.ExprSeq.eval

def eval {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Locals.Expr results)
    (state : σ) : Except EVMException (σ × List Word) :=
  Control.eval model prim expr state

namespace ExprSeq

def eval {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (exprs : Locals.ExprSeq results)
    (state : σ) : Except EVMException (σ × List Word) :=
  Control.ExprSeq.eval model prim exprs state

end ExprSeq

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
    change
      Control.eval model sourcePrim expr source =
        .ok (final, values) at hEval
    change
      Control.eval model targetPrim expr source =
        .ok (final, values)
    cases expr with
    | lit value =>
        simpa [Control.eval] using hEval
    | var name =>
        simpa [Control.eval] using hEval
    | code code =>
        simp [Control.eval] at hEval
    | prim op args =>
        simp only [Control.eval] at hEval ⊢
        cases hArgs :
            Control.ExprSeq.eval model sourcePrim args source with
        | error err =>
            simp [hArgs] at hEval
        | ok result =>
            rcases result with ⟨afterArgs, argValues⟩
            simp only [hArgs, Bind.bind, Except.bind] at hEval
            have hArgs' :
                Control.ExprSeq.eval model targetPrim args source =
                  .ok (afterArgs, argValues) :=
              by
                simpa [ExprSeq.eval] using
                  ExprSeq.eval_of_successRefines model hRefines
                    (show
                      ExprSeq.eval model sourcePrim args source =
                        .ok (afterArgs, argValues) from hArgs)
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
    change
      Control.ExprSeq.eval model sourcePrim exprs source =
        .ok (final, values) at hEval
    change
      Control.ExprSeq.eval model targetPrim exprs source =
        .ok (final, values)
    cases exprs with
    | nil =>
        simpa [Control.ExprSeq.eval] using hEval
    | @cons left right head tail =>
        simp only [Control.ExprSeq.eval] at hEval ⊢
        cases hHead : Control.eval model sourcePrim head source with
        | error err =>
            simp [hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨afterHead, headValues⟩
            simp only [hHead, Bind.bind, Except.bind] at hEval
            cases hTail :
                Control.ExprSeq.eval model sourcePrim tail afterHead with
            | error err =>
                simp [hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨tailFinal, tailValues⟩
                simp only [hTail, Bind.bind, Except.bind] at hEval
                have hHead' :
                    Control.eval model targetPrim head source =
                      .ok (afterHead, headValues) :=
                  by
                    simpa [eval] using
                      eval_of_successRefines model hRefines
                        (show
                          eval model sourcePrim head source =
                            .ok (afterHead, headValues) from hHead)
                have hTail' :
                    Control.ExprSeq.eval model targetPrim tail afterHead =
                      .ok (tailFinal, tailValues) :=
                  by
                    simpa [ExprSeq.eval] using
                      ExprSeq.eval_of_successRefines model hRefines
                        (show
                          ExprSeq.eval model sourcePrim tail afterHead =
                            .ok (tailFinal, tailValues) from hTail)
                simpa [hHead', hTail'] using hEval
end

def evalOne {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Locals.Expr results)
    (state : σ) : Except EVMException (σ × Word) :=
  Control.evalOne model prim expr state

def evalCondition {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Locals.Expr 1)
    (state : σ) : Except EVMException (σ × Bool) :=
  Control.evalCondition model prim expr state

theorem evalOne_of_successRefines
    {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
    (model : StateModel σ)
    (hRefines : sourcePrim.SuccessRefines targetPrim)
    {results : Nat} {expr : Locals.Expr results}
    {source final : σ} {value : Word}
    (hEval :
      evalOne model sourcePrim expr source = .ok (final, value)) :
    evalOne model targetPrim expr source = .ok (final, value) := by
  change
    Control.evalOne model sourcePrim expr source =
      .ok (final, value) at hEval
  change
    Control.evalOne model targetPrim expr source =
      .ok (final, value)
  simp only [Control.evalOne] at hEval ⊢
  cases hExpr : Control.eval model sourcePrim expr source with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨afterExpr, values⟩
      have hExpr' :
          Control.eval model targetPrim expr source =
            .ok (afterExpr, values) := by
        simpa [eval] using
          eval_of_successRefines model hRefines
            (show
              eval model sourcePrim expr source =
                .ok (afterExpr, values) from hExpr)
      simpa [hExpr, hExpr'] using hEval

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
  change
    Control.evalCondition model sourcePrim expr source =
      .ok (final, condition) at hEval
  change
    Control.evalCondition model targetPrim expr source =
      .ok (final, condition)
  simp only [Control.evalCondition] at hEval ⊢
  cases hExpr : Control.evalOne model sourcePrim expr source with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨afterExpr, value⟩
      have hExpr' :
          Control.evalOne model targetPrim expr source =
            .ok (afterExpr, value) := by
        simpa [evalOne] using
          evalOne_of_successRefines model hRefines
            (show
              evalOne model sourcePrim expr source =
                .ok (afterExpr, value) from hExpr)
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
        simp only [Effectful.Expr.eval, Expr.Control.eval,
          Source.Expr.eval]
        change
          (do
              let (stateAfterArgs, values) ←
                Effectful.Expr.ExprSeq.eval stateModel
                  (primitiveSemantics prim) args state
              (primitiveSemantics prim).eval
                op stateAfterArgs values) =
            (do
              let (stateAfterArgs, values) ←
                Source.Expr.ExprSeq.eval prim args state
              let (shared, values') ←
                prim.eval op stateAfterArgs.shared values
              .ok (stateAfterArgs.withShared shared, values'))
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
        simp only [Effectful.Expr.ExprSeq.eval,
          Expr.Control.ExprSeq.eval, Source.Expr.ExprSeq.eval]
        have hHeadEq :
            Expr.Control.eval stateModel (primitiveSemantics prim)
                head state =
              Source.Expr.eval prim head state := by
          simpa [Effectful.Expr.eval] using
            expr_eval_eq_source prim head state
        rw [hHeadEq]
        cases hHead : Source.Expr.eval prim head state with
        | error err =>
            simp [hHead]
        | ok result =>
            rcases result with ⟨stateAfterHead, values⟩
            simp only [hHead, Bind.bind, Except.bind]
            have hTailEq :
                Expr.Control.ExprSeq.eval stateModel
                    (primitiveSemantics prim) tail stateAfterHead =
                  Source.Expr.ExprSeq.eval prim tail stateAfterHead := by
              simpa [Effectful.Expr.ExprSeq.eval] using
                exprSeq_eval_eq_source prim tail stateAfterHead
            rw [hTailEq]
            rfl
end

end Ordinary

namespace Control

mutual
  def Block.runOpen {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Locals.Program)
      (ctx : Source.Ctx) : Nat → Locals.Block → σ →
      M (Outcome σ × Source.Ctx)
    | 0, _block, _state =>
        throw .InvalidInstruction
    | _fuel + 1, ⟨[]⟩, state =>
        pure (Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ←
          Stmt.run model prim program ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen model prim program ctx' fuel
              { stmts := rest } outcome.state
        | .brk | .cont | .leave | .halt _ =>
            pure (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Locals.Program)
      (ctx : Source.Ctx) (block : Locals.Block) (fuel : Nat)
      (state : σ) : M (Outcome σ) := do
    let (outcome, _) ←
      Block.runOpen model prim program ctx fuel block state
    match outcome.mode with
    | .regular =>
        pure (Outcome.regular (model.restrictTo ctx.scope outcome.state))
    | .brk | .cont | .leave | .halt _ =>
        pure outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def Stmt.runForLoop {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Locals.Program)
      (loopCtx : Source.Ctx) (cond : Locals.Expr 1)
      (postBase : Source.Ctx) (post : Locals.Block)
      (bodyBase : Source.Ctx) (body : Locals.Block) :
      Nat → σ → M (Outcome σ)
    | 0, _state =>
        throw .InvalidInstruction
    | fuel + 1, state => do
        let (stateAfterCond, condTrue) ←
          Expr.Control.evalCondition model prim cond state
        if condTrue then
          let bodyOutcome ←
            Block.runScoped model prim program bodyBase body fuel
              stateAfterCond
          match bodyOutcome.mode with
          | .brk =>
              pure (Outcome.regular bodyOutcome.state)
          | .regular | .cont => do
              let postOutcome ←
                Block.runScoped model prim program postBase post
                  fuel bodyOutcome.state
              match postOutcome.mode with
              | .regular =>
                  Stmt.runForLoop model prim program loopCtx cond
                    postBase post bodyBase body fuel postOutcome.state
              | .brk | .cont =>
                  throw .InvalidInstruction
              | .leave | .halt _ =>
                  pure postOutcome
          | .leave | .halt _ =>
              pure bodyOutcome
        else
          pure
            (Outcome.regular
              (model.restrictTo loopCtx.scope stateAfterCond))
  termination_by fuel _state => (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Locals.Program)
      (ctx : Source.Ctx) :
      Nat → Locals.Stmt → σ → M (Outcome σ × Source.Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ← Expr.Control.eval model prim expr state
        pure (Outcome.regular state', ctx)
    | _fuel, .exprs exprs, state => do
        let (state', _values) ←
          Expr.Control.ExprSeq.eval model prim exprs state
        pure (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ←
          Expr.Control.evalOne model prim value state
        pure
          (Outcome.regular (model.insert stateAfterValue name value'),
            { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if model.vars state |>.contains name then
          let (stateAfterValue, value') ←
            Expr.Control.evalOne model prim value state
          pure
            (Outcome.regular
              (model.withVars stateAfterValue
                (Source.Store.insert (model.vars stateAfterValue)
                  name value')),
              ctx)
        else
          throw .InvalidInstruction
    | _fuel, .assignTop _name, _state =>
        throw .InvalidInstruction
    | _fuel, .assignTopWithOffset _offset _name, _state =>
        throw .InvalidInstruction
    | _fuel, .promoteName _name, _state =>
        throw .InvalidInstruction
    | _fuel, .cleanupTo _targetLayout, _state =>
        throw .InvalidInstruction
    | fuel, .block body, state => do
        let outcome ←
          Block.runScoped model prim program ctx body fuel state
        pure (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        throw .InvalidInstruction
    | fuel + 1, .if_ cond body, state => do
        let (stateAfterCond, condTrue) ←
          Expr.Control.evalCondition model prim cond state
        if condTrue then do
          let outcome ←
            Block.runScoped model prim program ctx body fuel
              stateAfterCond
          pure (outcome, ctx)
        else
          pure (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        throw .InvalidInstruction
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let (stateAfterScrutinee, value) ←
          Expr.Control.evalOne model prim scrutinee state
        match Source.Switch.select value cases defaultBody with
        | none => pure (Outcome.regular stateAfterScrutinee, ctx)
        | some body =>
            let outcome ←
              Block.runScoped model prim program ctx body fuel
                stateAfterScrutinee
            pure (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        throw .InvalidInstruction
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
                pure
                  (Outcome.regular
                    (model.restrictTo ctx.scope loopOutcome.state),
                    ctx)
            | .brk | .cont =>
                throw .InvalidInstruction
            | .leave | .halt _ =>
                pure (loopOutcome, ctx)
        | .brk | .cont =>
            throw .InvalidInstruction
        | .leave | .halt _ =>
            pure (initOutcome, ctx)
    | _fuel, .brk, state =>
        match ctx.breakScope? with
        | none => throw .InvalidInstruction
        | some scope =>
            pure (Outcome.brk (model.restrictTo scope state), ctx)
    | _fuel, .cont, state =>
        match ctx.continueScope? with
        | none => throw .InvalidInstruction
        | some scope =>
            pure (Outcome.cont (model.restrictTo scope state), ctx)
    | _fuel, .leave, state =>
        match ctx.leaveScope? with
        | none => throw .InvalidInstruction
        | some scope =>
            pure (Outcome.leave (model.restrictTo scope state), ctx)
    | _fuel, .call _name, _state =>
        throw .InvalidInstruction
    | _fuel, .terminal kind, state => do
        let state' ← prim.terminal kind state []
        pure (Outcome.halt kind state', ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ←
          Expr.Control.ExprSeq.eval model prim args state
        let state' ← prim.terminal kind stateAfterArgs values
        pure (Outcome.halt kind state', ctx)
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

def runState {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) (fuel : Nat)
    (program : Locals.Program) (state : σ) : M (Outcome σ) :=
  Block.runScoped model prim program Source.Ctx.initial
    program.body fuel state

end Program

end Control

namespace Block

def runOpen {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Locals.Program)
    (ctx : Source.Ctx) (fuel : Nat) (block : Locals.Block)
    (state : σ) :
    Except EVMException (Outcome σ × Source.Ctx) :=
  Control.Block.runOpen model prim program ctx fuel block state

def runScoped {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Locals.Program)
    (ctx : Source.Ctx) (block : Locals.Block) (fuel : Nat)
    (state : σ) : Except EVMException (Outcome σ) :=
  Control.Block.runScoped model prim program ctx block fuel state

end Block

namespace Stmt

def runForLoop {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Locals.Program)
    (loopCtx : Source.Ctx) (cond : Locals.Expr 1)
    (postBase : Source.Ctx) (post : Locals.Block)
    (bodyBase : Source.Ctx) (body : Locals.Block)
    (fuel : Nat) (state : σ) : Except EVMException (Outcome σ) :=
  Control.Stmt.runForLoop model prim program loopCtx cond
    postBase post bodyBase body fuel state

def run {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Locals.Program)
    (ctx : Source.Ctx) (fuel : Nat) (stmt : Locals.Stmt)
    (state : σ) :
    Except EVMException (Outcome σ × Source.Ctx) :=
  Control.Stmt.run model prim program ctx fuel stmt state

end Stmt

namespace Program

def runState {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (program : Locals.Program) (state : σ) :
    Except EVMException (Outcome σ) :=
  Control.Program.runState model prim fuel program state

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
