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

@[simp] theorem regular_mode {σ : Type} (state : σ) :
    (regular state).mode = .regular := rfl

@[simp] theorem brk_mode {σ : Type} (state : σ) :
    (brk state).mode = .brk := rfl

@[simp] theorem cont_mode {σ : Type} (state : σ) :
    (cont state).mode = .cont := rfl

@[simp] theorem leave_mode {σ : Type} (state : σ) :
    (leave state).mode = .leave := rfl

@[simp] theorem halt_mode {σ : Type}
    (kind : Assembly.HaltKind) (state : σ) :
    (halt kind state).mode = .halt kind := rfl

theorem brk_not_regular {σ : Type} (state : σ) :
    (brk state).mode ≠ .regular := by
  simp

theorem cont_not_regular {σ : Type} (state : σ) :
    (cont state).mode ≠ .regular := by
  simp

theorem leave_not_regular {σ : Type} (state : σ) :
    (leave state).mode ≠ .regular := by
  simp

theorem halt_not_regular {σ : Type}
    (kind : Assembly.HaltKind) (state : σ) :
    (halt kind state).mode ≠ .regular := by
  simp

def IsExit {σ : Type} (outcome : Outcome σ) : Prop :=
  match outcome.mode with
  | .leave | .halt _ => True
  | .regular | .brk | .cont => False

theorem eq_regular_of_mode {σ : Type} {outcome : Outcome σ}
    (hMode : outcome.mode = .regular) :
    outcome = regular outcome.state := by
  rcases outcome with ⟨state, mode⟩
  change mode = .regular at hMode
  subst mode
  rfl

theorem eq_brk_of_mode {σ : Type} {outcome : Outcome σ}
    (hMode : outcome.mode = .brk) :
    outcome = brk outcome.state := by
  rcases outcome with ⟨state, mode⟩
  change mode = .brk at hMode
  subst mode
  rfl

theorem eq_cont_of_mode {σ : Type} {outcome : Outcome σ}
    (hMode : outcome.mode = .cont) :
    outcome = cont outcome.state := by
  rcases outcome with ⟨state, mode⟩
  change mode = .cont at hMode
  subst mode
  rfl

theorem eq_leave_of_mode {σ : Type} {outcome : Outcome σ}
    (hMode : outcome.mode = .leave) :
    outcome = leave outcome.state := by
  rcases outcome with ⟨state, mode⟩
  change mode = .leave at hMode
  subst mode
  rfl

theorem IsExit.not_regular {σ : Type} {outcome : Outcome σ}
    (hExit : IsExit outcome) :
    outcome.mode ≠ .regular := by
  rcases outcome with ⟨state, mode⟩
  cases mode <;> simp [IsExit] at hExit ⊢

theorem IsExit.ne_brk {σ : Type} {outcome : Outcome σ}
    (hExit : IsExit outcome) (state : σ) :
    outcome ≠ brk state := by
  intro hOutcome
  subst outcome
  simp [IsExit] at hExit

theorem IsExit.ne_cont {σ : Type} {outcome : Outcome σ}
    (hExit : IsExit outcome) (state : σ) :
    outcome ≠ cont state := by
  intro hOutcome
  subst outcome
  simp [IsExit] at hExit

end Outcome

namespace Expr

abbrev eval {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Functions.Expr results)
    (state : σ) : Except EVMException (σ × List Word) :=
  Locals.Source.Effectful.Expr.Control.eval model prim expr state

abbrev evalOne {σ : Type} {results : Nat} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Functions.Expr results)
    (state : σ) : Except EVMException (σ × Word) :=
  Locals.Source.Effectful.Expr.Control.evalOne model prim expr state

abbrev evalCondition {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (expr : Functions.Expr 1)
    (state : σ) : Except EVMException (σ × Bool) :=
  Locals.Source.Effectful.Expr.Control.evalCondition model prim expr state

theorem eval_var {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {name : Name} {state : σ} {value : Word}
    (hLookup : model.vars state name = some value) :
    eval model prim (.var name : Functions.Expr 1) state =
      .ok (state, [value]) := by
  simp [eval, Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.Control.eval, hLookup]

theorem evalOne_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value])) :
    evalOne model prim expr state =
      .ok (final, value) := by
  have hEvalControl :
      Locals.Source.Effectful.Expr.Control.eval
          model prim expr state =
        .ok (final, [value]) := by
    simpa [eval, Locals.Source.Effectful.Expr.eval] using hEval
  simp [evalOne, Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.Control.evalOne,
    hEvalControl]

theorem evalCondition_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value])) :
    evalCondition model prim expr state =
      .ok (final, value != EvmYul.UInt256.ofNat 0) := by
  have hEvalControl :
      Locals.Source.Effectful.Expr.Control.eval
          model prim expr state =
        .ok (final, [value]) := by
    simpa [eval, Locals.Source.Effectful.Expr.eval] using hEval
  simp [evalCondition, Locals.Source.Effectful.Expr.evalCondition,
    Locals.Source.Effectful.Expr.Control.evalCondition,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.Control.evalOne,
    hEvalControl]

theorem evalCondition_false_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value]))
    (hZero : value = EvmYul.UInt256.ofNat 0) :
    evalCondition model prim expr state =
      .ok (final, false) := by
  subst value
  simpa using evalCondition_of_eval_singleton model prim hEval

theorem evalCondition_true_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value]))
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0) :
    evalCondition model prim expr state =
      .ok (final, true) := by
  have hBne :
      (value != EvmYul.UInt256.ofNat 0) = true := by
    cases value with
    | mk value =>
        simp [bne, EvmYul.instBEqUInt256,
          EvmYul.instBEqUInt256.beq,
          EvmYul.UInt256.ofNat, Id.run] at hNonzero ⊢
        exact hNonzero
  simpa [hBne] using evalCondition_of_eval_singleton model prim hEval

theorem evalCondition_iszero_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value]))
    (hIszero :
      prim.eval .iszero final [value] =
        .ok (final, [EvmYul.UInt256.isZero value])) :
    evalCondition model prim
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      .ok
        (final,
          EvmYul.UInt256.isZero value != EvmYul.UInt256.ofNat 0) := by
  have hEvalControl :
      Locals.Source.Effectful.Expr.Control.eval
          model prim expr state =
        .ok (final, [value]) := by
    simpa [eval, Locals.Source.Effectful.Expr.eval] using hEval
  simp [evalCondition, Locals.Source.Effectful.Expr.evalCondition,
    Locals.Source.Effectful.Expr.Control.evalCondition,
    Locals.Source.Effectful.Expr.evalOne, eval,
    Locals.Source.Effectful.Expr.Control.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.Control.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    Locals.Source.Effectful.Expr.Control.ExprSeq.eval,
    hEvalControl, hIszero]

theorem evalCondition_iszero_true_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value]))
    (hIszero :
      prim.eval .iszero final [value] =
        .ok (final, [EvmYul.UInt256.isZero value]))
    (hZero : value = EvmYul.UInt256.ofNat 0) :
    evalCondition model prim
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      .ok (final, true) := by
  subst value
  simpa using
    evalCondition_iszero_of_eval_singleton model prim hEval hIszero

theorem evalCondition_iszero_false_of_eval_singleton {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      eval model prim expr state =
        .ok (final, [value]))
    (hIszero :
      prim.eval .iszero final [value] =
        .ok (final, [EvmYul.UInt256.isZero value]))
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0) :
    evalCondition model prim
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      .ok (final, false) := by
  have hEq0 : EvmYul.UInt256.eq0 value = false := by
    cases value with
    | mk value =>
        simp [EvmYul.UInt256.eq0, EvmYul.instBEqUInt256,
          EvmYul.instBEqUInt256.beq, EvmYul.UInt256.ofNat, Id.run]
          at hNonzero ⊢
        exact hNonzero
  have hIszeroZero :
      EvmYul.UInt256.isZero value = EvmYul.UInt256.ofNat 0 := by
    simp [EvmYul.UInt256.isZero, hEq0, EvmYul.UInt256.fromBool]
  simpa [hIszeroZero] using
    evalCondition_iszero_of_eval_singleton model prim hEval hIszero

end Expr

attribute [simp] Expr.eval Expr.evalOne Expr.evalCondition

namespace ArgList

namespace Control

def eval {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : Locals.Source.Effectful.Control.PrimitiveSemantics M σ) :
    List (Functions.Expr 1) → σ → M (σ × List Word)
  | [], state => pure (state, [])
  | arg :: rest, state => do
      let (stateAfterArg, value) ←
        Locals.Source.Effectful.Expr.Control.evalOne model prim arg state
      let (stateAfterRest, values) ←
        eval model prim rest stateAfterArg
      pure (stateAfterRest, value :: values)

end Control

attribute [simp] Control.eval

def eval {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) :
    List (Functions.Expr 1) → σ →
      Except EVMException (σ × List Word) :=
  Control.eval model prim

theorem eval_length {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) :
    ∀ {args : List (Functions.Expr 1)} {state state' : σ}
      {values : List Word},
      eval model prim args state = .ok (state', values) →
        values.length = args.length
  | [], _state, _state', _values, hEval => by
      cases hEval
      rfl
  | arg :: rest, state, state', values, hEval => by
      unfold eval at hEval
      cases hArg : Expr.evalOne model prim arg state with
      | error err =>
          simp [hArg] at hEval
      | ok argResult =>
          rcases argResult with ⟨stateAfterArg, value⟩
          simp [hArg] at hEval
          cases hRest : Control.eval model prim rest stateAfterArg with
          | error err =>
              simp [hRest] at hEval
          | ok restResult =>
              rcases restResult with ⟨stateAfterRest, restValues⟩
              simp [hRest] at hEval
              rcases hEval with ⟨_hStateEq, hValuesEq⟩
              have hTail :=
                eval_length model prim
                  (args := rest) (state := stateAfterArg)
                  (state' := stateAfterRest) (values := restValues) hRest
              rw [← hValuesEq]
              simp [hTail]

theorem eval_append
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) :
    ∀ {left right : List (Functions.Expr 1)}
      {source middle final : σ}
      {leftValues rightValues : List Word},
      eval model prim left source = .ok (middle, leftValues) →
      eval model prim right middle = .ok (final, rightValues) →
      eval model prim (left ++ right) source =
        .ok (final, leftValues ++ rightValues)
  | [], right, source, middle, final, leftValues, rightValues,
      hLeft, hRight => by
      simp [eval] at hLeft
      rcases hLeft with ⟨rfl, rfl⟩
      simpa [eval] using hRight
  | head :: rest, right, source, middle, final, leftValues, rightValues,
      hLeft, hRight => by
      unfold eval at hLeft ⊢
      cases hHead : Expr.evalOne model prim head source with
      | error err =>
          simp [hHead] at hLeft
      | ok headResult =>
          rcases headResult with ⟨stateAfterHead, value⟩
          simp [hHead] at hLeft ⊢
          cases hRest : Control.eval model prim rest stateAfterHead with
          | error err =>
              simp [hRest] at hLeft
          | ok restResult =>
              rcases restResult with ⟨stateAfterRest, restValues⟩
              simp [hRest] at hLeft
              rcases hLeft with ⟨rfl, rfl⟩
              have hTail :=
                eval_append model prim hRest hRight
              have hTailControl :
                  Control.eval model prim (rest ++ right) stateAfterHead =
                    .ok (final, restValues ++ rightValues) := by
                simpa [eval] using hTail
              rw [hTailControl]
              simp

theorem eval_of_successRefines
    {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
    (model : StateModel σ)
    (hRefines : sourcePrim.SuccessRefines targetPrim) :
    ∀ {args : List (Functions.Expr 1)} {source final : σ}
      {values : List Word},
      eval model sourcePrim args source = .ok (final, values) →
        eval model targetPrim args source = .ok (final, values)
  | [], _source, _final, _values, hEval => by
      simpa [eval] using hEval
  | arg :: rest, source, final, values, hEval => by
      unfold eval at hEval ⊢
      cases hArg : Expr.evalOne model sourcePrim arg source with
      | error err =>
          simp [hArg] at hEval
      | ok argResult =>
          rcases argResult with ⟨afterArg, value⟩
          simp [hArg] at hEval
          cases hRest : Control.eval model sourcePrim rest afterArg with
          | error err =>
              simp [hRest] at hEval
          | ok restResult =>
              rcases restResult with ⟨restFinal, restValues⟩
              simp only [hRest, Bind.bind, Except.bind] at hEval
              have hArg' :
                  Expr.evalOne model targetPrim arg source =
                    .ok (afterArg, value) :=
                Locals.Source.Effectful.Expr.evalOne_of_successRefines
                  model hRefines hArg
              have hRest' :
                  eval model targetPrim rest afterArg =
                    .ok (restFinal, restValues) :=
                eval_of_successRefines model hRefines hRest
              have hRestControl :
                  Control.eval model targetPrim rest afterArg =
                    .ok (restFinal, restValues) := by
                simpa [eval] using hRest'
              rcases hEval with ⟨rfl, rfl⟩
              simp [hArg', hRestControl]

end ArgList

inductive CallResult (σ : Type) where
  | returned (state : σ) (values : List Word)
  | halted (kind : Assembly.HaltKind) (state : σ)

namespace Control

abbrev PrimitiveSemantics (M : Type → Type) (σ : Type) :=
  Locals.Source.Effectful.Control.PrimitiveSemantics M σ

mutual
  def Block.runOpen {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Functions.Program)
      (ctx : Source.Ctx) : Nat → Functions.Block → σ →
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
      (prim : PrimitiveSemantics M σ) (program : Functions.Program)
      (ctx : Source.Ctx) (block : Functions.Block) (fuel : Nat)
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

  def FunDef.runBody {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Functions.Program)
      (fn : Functions.FunDef) (args : List Word) :
      Nat → σ → M (CallResult σ)
    | 0, _state =>
        throw .InvalidInstruction
    | fuel + 1, state => do
        let paramStore ←
          (Source.Store.insertMany fn.params args
            Locals.Source.Store.empty).elim
              (throw .InvalidInstruction) pure
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
                (model.vars bodyOutcome.state)).elim
                  (throw .InvalidInstruction) pure
            pure (.returned bodyOutcome.state values)
        | .brk | .cont =>
            throw .InvalidInstruction
        | .halt kind =>
            pure (.halted kind bodyOutcome.state)
  termination_by fuel _state => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runForLoop {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Functions.Program)
      (loopCtx : Source.Ctx) (cond : Functions.Expr 1)
      (postBase : Source.Ctx) (post : Functions.Block)
      (bodyBase : Source.Ctx) (body : Functions.Block) :
      Nat → σ → M (Outcome σ)
    | 0, _state =>
        throw .InvalidInstruction
    | fuel + 1, state => do
        let (stateAfterCond, condTrue) ←
          Locals.Source.Effectful.Expr.Control.evalCondition
            model prim cond state
        if condTrue then
          let bodyOutcome ←
            Block.runScoped model prim program bodyBase body fuel
              stateAfterCond
          match bodyOutcome.mode with
          | .brk =>
              pure (Outcome.regular bodyOutcome.state)
          | .regular | .cont => do
              let postOutcome ←
                Block.runScoped model prim program postBase post fuel
                  bodyOutcome.state
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
  termination_by fuel _state => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run {M : Type → Type} [Monad M]
      [MonadExceptOf EVMException M]
      {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics M σ) (program : Functions.Program)
      (ctx : Source.Ctx) : Nat → Functions.Stmt → σ →
      M (Outcome σ × Source.Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ←
          Locals.Source.Effectful.Expr.Control.eval model prim expr state
        pure (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ←
          Locals.Source.Effectful.Expr.Control.evalOne
            model prim value state
        pure
          (Outcome.regular (model.insert stateAfterValue name value'),
            { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if model.vars state |>.contains name then
          let (stateAfterValue, value') ←
            Locals.Source.Effectful.Expr.Control.evalOne
              model prim value state
          pure
            (Outcome.regular
              (model.withVars stateAfterValue
                (Locals.Source.Store.insert
                  (model.vars stateAfterValue) name value')),
              ctx)
        else
          throw .InvalidInstruction
    | fuel, .block body, state => do
        let outcome ←
          Block.runScoped model prim program ctx body fuel state
        pure (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        throw .InvalidInstruction
    | fuel + 1, .if_ cond body, state => do
        let (stateAfterCond, condTrue) ←
          Locals.Source.Effectful.Expr.Control.evalCondition
            model prim cond state
        if condTrue then do
          let outcome ←
            Block.runScoped model prim program ctx body fuel stateAfterCond
          pure (outcome, ctx)
        else
          pure (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        throw .InvalidInstruction
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let (stateAfterScrutinee, value) ←
          Locals.Source.Effectful.Expr.Control.evalOne
            model prim scrutinee state
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
    | 0, .call _targets _functionName _args, _state =>
        throw .InvalidInstruction
    | fuel + 1, .call targets functionName args, state => do
        if targets.Nodup then
          let (stateAfterArgs, argValues) ←
            ArgList.Control.eval model prim args state
          let fn ←
            (Source.FunList.find? functionName program.functions).elim
              (throw .InvalidInstruction) pure
          let callResult ←
            FunDef.runBody model prim program fn argValues fuel
              stateAfterArgs
          match callResult with
          | .returned stateAfterCall returnValues =>
              let returnStore ←
                (Source.Store.assignMany targets returnValues
                  (model.vars stateAfterArgs)).elim
                    (throw .InvalidInstruction) pure
              let returnedSource := model.source stateAfterCall
              pure
                (Outcome.regular
                  (model.withSource stateAfterCall
                    { shared := returnedSource.shared,
                      vars := returnStore }),
                  ctx)
          | .halted kind haltedState =>
              pure (Outcome.halt kind haltedState, ctx)
        else
          throw .InvalidInstruction
    | _fuel, .terminal kind, state => do
        let state' ← prim.terminal kind state []
        pure (Outcome.halt kind state', ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ←
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
            model prim args state
        let state' ← prim.terminal kind stateAfterArgs values
        pure (Outcome.halt kind state', ctx)
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

def runState {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) (fuel : Nat)
    (program : Functions.Program) (state : σ) : M (Outcome σ) :=
  Block.runScoped model prim program Source.Ctx.initial
    program.body fuel state

end Program
end Control

attribute [simp]
  Control.Block.runOpen Control.Stmt.run

abbrev Block.runOpen {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Functions.Program)
    (ctx : Source.Ctx) (fuel : Nat) (block : Functions.Block) (state : σ) :
    Except EVMException (Outcome σ × Source.Ctx) :=
  Control.Block.runOpen model prim program ctx fuel block state

abbrev Block.runScoped {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Functions.Program)
    (ctx : Source.Ctx) (block : Functions.Block) (fuel : Nat)
    (state : σ) : Except EVMException (Outcome σ) :=
  Control.Block.runScoped model prim program ctx block fuel state

abbrev FunDef.runBody {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Functions.Program)
    (fn : Functions.FunDef) (args : List Word) (fuel : Nat) (state : σ) :
    Except EVMException (CallResult σ) :=
  Control.FunDef.runBody model prim program fn args fuel state

abbrev Stmt.runForLoop {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Functions.Program)
    (loopCtx : Source.Ctx) (cond : Functions.Expr 1)
    (postBase : Source.Ctx) (post : Functions.Block)
    (bodyBase : Source.Ctx) (body : Functions.Block)
    (fuel : Nat) (state : σ) : Except EVMException (Outcome σ) :=
  Control.Stmt.runForLoop model prim program loopCtx cond
    postBase post bodyBase body fuel state

abbrev Stmt.run {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (program : Functions.Program)
    (ctx : Source.Ctx) (fuel : Nat) (stmt : Functions.Stmt) (state : σ) :
    Except EVMException (Outcome σ × Source.Ctx) :=
  Control.Stmt.run model prim program ctx fuel stmt state

attribute [simp]
  Block.runOpen Block.runScoped FunDef.runBody Stmt.runForLoop Stmt.run

/--
Successful statement execution never removes names from the open lexical
context. Statements other than `let` return the incoming context; `let`
extends it by one binding.
-/
theorem Stmt.run_scopeExtends
    {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {stmt : Stmt} {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx fuel stmt source =
        .ok (outcome, finalCtx)) :
    Source.Ctx.ScopeExtends ctx finalCtx := by
  cases stmt with
  | expr expr =>
      unfold Control.Stmt.run at hRun
      cases hExpr : Expr.eval model prim expr source with
      | error err => simp [hExpr] at hRun
      | ok result =>
          rcases result with ⟨final, values⟩
          have hPair :
              (Outcome.regular final, ctx) = (outcome, finalCtx) := by
            simpa [hExpr] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
  | let_ name value =>
      unfold Control.Stmt.run at hRun
      cases hValue : Expr.evalOne model prim value source with
      | error err => simp [hValue] at hRun
      | ok result =>
          rcases result with ⟨afterValue, value'⟩
          have hPair :
              (Outcome.regular (model.insert afterValue name value'),
                  { ctx with scope := name :: ctx.scope }) =
                (outcome, finalCtx) := by
            simpa [hValue] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.cons ctx name
  | assign name value =>
      unfold Control.Stmt.run at hRun
      by_cases hContains : (model.vars source).contains name
      · simp only [hContains, Bool.true_eq, ↓reduceIte] at hRun
        cases hValue : Expr.evalOne model prim value source with
        | error err => simp [hValue] at hRun
        | ok result =>
            rcases result with ⟨afterValue, value'⟩
            have hPair :
                (Outcome.regular
                    (model.withVars afterValue
                      ((model.vars afterValue).insert name value')),
                    ctx) =
                  (outcome, finalCtx) := by
              simpa [hValue] using hRun
            injection hPair with _ hCtx
            subst finalCtx
            exact Source.Ctx.ScopeExtends.refl ctx
      · simp [hContains, Source.invalid, Structured.invalid] at hRun
  | block body =>
      unfold Control.Stmt.run at hRun
      cases hBody :
          Control.Block.runScoped model prim program ctx body fuel source with
      | error err => simp [hBody] at hRun
      | ok bodyOutcome =>
          have hPair :
              (bodyOutcome, ctx) = (outcome, finalCtx) := by
            simpa [hBody] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
  | if_ cond body =>
      cases fuel with
      | zero =>
          simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Control.Stmt.run at hRun
          cases hCond : Expr.evalCondition model prim cond source with
          | error err => simp [hCond] at hRun
          | ok condResult =>
              rcases condResult with ⟨afterCond, condTrue⟩
              cases condTrue with
              | false =>
                  have hPair :
                      (Outcome.regular afterCond, ctx) =
                        (outcome, finalCtx) := by
                    simpa [hCond] using hRun
                  injection hPair with _ hCtx
                  subst finalCtx
                  exact Source.Ctx.ScopeExtends.refl ctx
              | true =>
                  cases hBody :
                      Control.Block.runScoped model prim program ctx body fuel
                        afterCond with
                  | error err => simp [hCond, hBody] at hRun
                  | ok bodyOutcome =>
                      have hPair :
                          (bodyOutcome, ctx) = (outcome, finalCtx) := by
                        simpa [hCond, hBody] using hRun
                      injection hPair with _ hCtx
                      subst finalCtx
                      exact Source.Ctx.ScopeExtends.refl ctx
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Control.Stmt.run at hRun
          cases hScrutinee :
              Expr.evalOne model prim scrutinee source with
          | error err => simp [hScrutinee] at hRun
          | ok scrutineeResult =>
              rcases scrutineeResult with ⟨afterScrutinee, value⟩
              cases hSelected :
                  Source.Switch.select value cases defaultBody with
              | none =>
                  have hPair :
                      (Outcome.regular afterScrutinee, ctx) =
                        (outcome, finalCtx) := by
                    simpa [hScrutinee, hSelected] using hRun
                  injection hPair with _ hCtx
                  subst finalCtx
                  exact Source.Ctx.ScopeExtends.refl ctx
              | some selected =>
                  cases hBody :
                      Control.Block.runScoped model prim program ctx selected fuel
                        afterScrutinee with
                  | error err =>
                      simp [hScrutinee, hSelected, hBody] at hRun
                  | ok bodyOutcome =>
                      have hPair :
                          (bodyOutcome, ctx) = (outcome, finalCtx) := by
                        simpa [hScrutinee, hSelected, hBody] using hRun
                      injection hPair with _ hCtx
                      subst finalCtx
                      exact Source.Ctx.ScopeExtends.refl ctx
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Control.Stmt.run at hRun
          let initBase := ctx.withoutLoopControl
          cases hInit :
              Control.Block.runOpen model prim program initBase fuel init source with
          | error err => simp [initBase, hInit] at hRun
          | ok initResult =>
              rcases initResult with ⟨initOutcome, initCtx⟩
              cases hInitMode : initOutcome.mode with
              | regular =>
                  let loopCtx := initCtx
                  let postBase := initCtx.withoutLoopControl
                  let bodyBase :=
                    initCtx.withLoopControl initCtx.scope initCtx.scope
                  cases hLoop :
                      Control.Stmt.runForLoop model prim program loopCtx cond
                        postBase post bodyBase body fuel initOutcome.state with
                  | error err =>
                      simp [initBase, hInit, hInitMode, loopCtx,
                        postBase, bodyBase, hLoop] at hRun
                  | ok loopOutcome =>
                      cases hLoopMode : loopOutcome.mode with
                      | regular =>
                          have hPair :
                              (Outcome.regular
                                  (model.restrictTo ctx.scope
                                    loopOutcome.state),
                                  ctx) =
                                (outcome, finalCtx) := by
                            simpa [initBase, hInit, hInitMode, loopCtx,
                              postBase, bodyBase, hLoop, hLoopMode] using hRun
                          injection hPair with _ hCtx
                          subst finalCtx
                          exact Source.Ctx.ScopeExtends.refl ctx
                      | brk =>
                          simp [initBase, hInit, hInitMode, loopCtx,
                            postBase, bodyBase, hLoop, hLoopMode,
                            Source.invalid, Structured.invalid] at hRun
                      | cont =>
                          simp [initBase, hInit, hInitMode, loopCtx,
                            postBase, bodyBase, hLoop, hLoopMode,
                            Source.invalid, Structured.invalid] at hRun
                      | leave =>
                          have hPair :
                              (loopOutcome, ctx) = (outcome, finalCtx) := by
                            simpa [initBase, hInit, hInitMode, loopCtx,
                              postBase, bodyBase, hLoop, hLoopMode] using hRun
                          injection hPair with _ hCtx
                          subst finalCtx
                          exact Source.Ctx.ScopeExtends.refl ctx
                      | halt kind =>
                          have hPair :
                              (loopOutcome, ctx) = (outcome, finalCtx) := by
                            simpa [initBase, hInit, hInitMode, loopCtx,
                              postBase, bodyBase, hLoop, hLoopMode] using hRun
                          injection hPair with _ hCtx
                          subst finalCtx
                          exact Source.Ctx.ScopeExtends.refl ctx
              | brk =>
                  simp [initBase, hInit, hInitMode,
                    Source.invalid, Structured.invalid] at hRun
              | cont =>
                  simp [initBase, hInit, hInitMode,
                    Source.invalid, Structured.invalid] at hRun
              | leave =>
                  have hPair :
                      (initOutcome, ctx) = (outcome, finalCtx) := by
                    simpa [initBase, hInit, hInitMode] using hRun
                  injection hPair with _ hCtx
                  subst finalCtx
                  exact Source.Ctx.ScopeExtends.refl ctx
              | halt kind =>
                  have hPair :
                      (initOutcome, ctx) = (outcome, finalCtx) := by
                    simpa [initBase, hInit, hInitMode] using hRun
                  injection hPair with _ hCtx
                  subst finalCtx
                  exact Source.Ctx.ScopeExtends.refl ctx
  | brk =>
      unfold Control.Stmt.run at hRun
      cases hScope : ctx.breakScope? with
      | none => simp [hScope, Source.invalid, Structured.invalid] at hRun
      | some scope =>
          have hPair :
              (Outcome.brk (model.restrictTo scope source), ctx) =
                (outcome, finalCtx) := by
            simpa [hScope] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
  | cont =>
      unfold Control.Stmt.run at hRun
      cases hScope : ctx.continueScope? with
      | none => simp [hScope, Source.invalid, Structured.invalid] at hRun
      | some scope =>
          have hPair :
              (Outcome.cont (model.restrictTo scope source), ctx) =
                (outcome, finalCtx) := by
            simpa [hScope] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
  | leave =>
      unfold Control.Stmt.run at hRun
      cases hScope : ctx.leaveScope? with
      | none => simp [hScope, Source.invalid, Structured.invalid] at hRun
      | some scope =>
          have hPair :
              (Outcome.leave (model.restrictTo scope source), ctx) =
                (outcome, finalCtx) := by
            simpa [hScope] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
  | call targets functionName args =>
      cases fuel with
      | zero =>
          simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Control.Stmt.run at hRun
          by_cases hTargets : targets.Nodup
          · simp only [hTargets, Bool.true_eq, ↓reduceIte] at hRun
            cases hArgs : ArgList.Control.eval model prim args source with
            | error err => simp [hArgs] at hRun
            | ok argResult =>
                rcases argResult with ⟨afterArgs, argValues⟩
                cases hLookup :
                    Source.FunList.find? functionName program.functions with
                | none =>
                    simp [hArgs, hLookup, Source.invalid,
                      Structured.invalid] at hRun
                | some fn =>
                    cases hBody :
                        Control.FunDef.runBody model prim program fn argValues fuel
                          afterArgs with
                    | error err => simp [hArgs, hLookup, hBody] at hRun
                    | ok callResult =>
                        cases callResult with
                        | returned afterCall returnValues =>
                            cases hAssign :
                                Source.Store.assignMany targets returnValues
                                  (model.vars afterArgs) with
                            | none =>
                                simp [hArgs, hLookup, hBody, hAssign,
                                  Source.invalid, Structured.invalid] at hRun
                            | some returnStore =>
                                have hPair :
                                    (Outcome.regular
                                        (model.withSource afterCall
                                          { shared :=
                                              (model.source afterCall).shared,
                                            vars := returnStore }),
                                        ctx) =
                                      (outcome, finalCtx) := by
                                  simpa [hArgs, hLookup, hBody, hAssign]
                                    using hRun
                                injection hPair with _ hCtx
                                subst finalCtx
                                exact Source.Ctx.ScopeExtends.refl ctx
                        | halted kind haltedState =>
                            have hPair :
                                (Outcome.halt kind haltedState, ctx) =
                                  (outcome, finalCtx) := by
                              simpa [hArgs, hLookup, hBody] using hRun
                            injection hPair with _ hCtx
                            subst finalCtx
                            exact Source.Ctx.ScopeExtends.refl ctx
          · simp [hTargets, Source.invalid, Structured.invalid] at hRun
  | terminal kind =>
      unfold Control.Stmt.run at hRun
      cases hTerminal : prim.terminal kind source [] with
      | error err => simp [hTerminal] at hRun
      | ok final =>
          have hPair :
              (Outcome.halt kind final, ctx) = (outcome, finalCtx) := by
            simpa [hTerminal] using hRun
          injection hPair with _ hCtx
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
  | terminalArgs kind args =>
      unfold Control.Stmt.run at hRun
      cases hArgs :
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
            model prim args source with
      | error err => simp [hArgs] at hRun
      | ok argResult =>
          rcases argResult with ⟨afterArgs, values⟩
          cases hTerminal : prim.terminal kind afterArgs values with
          | error err => simp [hArgs, hTerminal] at hRun
          | ok final =>
              have hPair :
                  (Outcome.halt kind final, ctx) =
                    (outcome, finalCtx) := by
                simpa [hArgs, hTerminal] using hRun
              injection hPair with _ hCtx
              subst finalCtx
              exact Source.Ctx.ScopeExtends.refl ctx

set_option maxHeartbeats 1000000 in
mutual
  /--
  Successful open-block execution is preserved when every successful primitive
  effect is reproduced by the target primitive semantics.
  -/
  theorem Block.runOpen_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      (program : Program) :
      ∀ {fuel : Nat} {ctx : Source.Ctx} {block : Block}
        {state : σ} {outcome : Outcome σ} {runCtx : Source.Ctx},
        Control.Block.runOpen model sourcePrim program ctx fuel block state =
          .ok (outcome, runCtx) →
        Control.Block.runOpen model targetPrim program ctx fuel block state =
          .ok (outcome, runCtx) := by
    intro fuel ctx block state outcome runCtx hRun
    cases fuel with
    | zero =>
        cases block
        simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simpa [Control.Block.runOpen] using hRun
            | cons stmt rest =>
                cases hStmt :
                    Control.Stmt.run model sourcePrim program ctx fuel stmt state with
                | error err =>
                    simp [Control.Block.runOpen, hStmt] at hRun
                | ok stmtResult =>
                    rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                    have hStmt' :
                        Control.Stmt.run model targetPrim program ctx fuel stmt state =
                          .ok (stmtOutcome, stmtCtx) :=
                      Stmt.run_of_successRefines
                        model hRefines program hStmt
                    cases hMode : stmtOutcome.mode with
                    | regular =>
                        simp [Control.Block.runOpen, hStmt, hStmt', hMode]
                          at hRun ⊢
                        exact
                          Block.runOpen_of_successRefines
                            model hRefines program hRun
                    | brk =>
                        simpa [Control.Block.runOpen, hStmt, hStmt', hMode] using hRun
                    | cont =>
                        simpa [Control.Block.runOpen, hStmt, hStmt', hMode] using hRun
                    | leave =>
                        simpa [Control.Block.runOpen, hStmt, hStmt', hMode] using hRun
                    | halt kind =>
                        simpa [Control.Block.runOpen, hStmt, hStmt', hMode] using hRun
  termination_by
    fuel _ctx block _state _outcome _runCtx _hRun =>
      (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      (program : Program) :
      ∀ {fuel : Nat} {ctx : Source.Ctx} {block : Block}
        {state : σ} {outcome : Outcome σ},
        Control.Block.runScoped model sourcePrim program ctx block fuel state =
          .ok outcome →
        Control.Block.runScoped model targetPrim program ctx block fuel state =
          .ok outcome := by
    intro fuel ctx block state outcome hRun
    unfold Control.Block.runScoped at hRun ⊢
    cases hOpen :
        Control.Block.runOpen model sourcePrim program ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        have hOpen' :
            Control.Block.runOpen model targetPrim program ctx fuel block state =
              .ok (openOutcome, finalCtx) :=
          Block.runOpen_of_successRefines model hRefines program hOpen
        cases hMode : openOutcome.mode with
        | regular =>
            simpa [hOpen, hOpen', hMode] using hRun
        | brk =>
            simpa [hOpen, hOpen', hMode] using hRun
        | cont =>
            simpa [hOpen, hOpen', hMode] using hRun
        | leave =>
            simpa [hOpen, hOpen', hMode] using hRun
        | halt kind =>
            simpa [hOpen, hOpen', hMode] using hRun
  termination_by
    fuel _ctx block _state _outcome _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right fuel
          (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  theorem FunDef.runBody_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      (program : Program) :
      ∀ {fuel : Nat} {fn : FunDef} {args : List Word}
        {state : σ} {result : CallResult σ},
        Control.FunDef.runBody model sourcePrim program fn args fuel state =
          .ok result →
        Control.FunDef.runBody model targetPrim program fn args fuel state =
          .ok result := by
    intro fuel fn args state result hRun
    cases fuel with
    | zero =>
        simp [Control.FunDef.runBody, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases hParams :
            Source.Store.insertMany fn.params args
              Locals.Source.Store.empty with
        | none =>
            simp [Control.FunDef.runBody, hParams, Source.invalid,
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
                Control.Block.runOpen model sourcePrim program bodyCtx fuel fn.body
                  initialState with
            | error err =>
                simp [Control.FunDef.runBody, hParams, initialStore,
                  callerSource, initialSource, initialState,
                  functionScope, bodyCtx, hBody] at hRun
            | ok bodyResult =>
                rcases bodyResult with ⟨bodyOutcome, bodyFinalCtx⟩
                have hBody' :
                    Control.Block.runOpen model targetPrim program bodyCtx fuel fn.body
                        initialState =
                      .ok (bodyOutcome, bodyFinalCtx) :=
                  Block.runOpen_of_successRefines
                    model hRefines program hBody
                cases hMode : bodyOutcome.mode with
                | regular =>
                    simpa [Control.FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody, hBody', hMode] using hRun
                | brk =>
                    simp [Control.FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody, hBody', hMode,
                      Source.invalid, Structured.invalid] at hRun
                | cont =>
                    simp [Control.FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody, hBody', hMode,
                      Source.invalid, Structured.invalid] at hRun
                | leave =>
                    simpa [Control.FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody, hBody', hMode] using hRun
                | halt kind =>
                    simpa [Control.FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody, hBody', hMode] using hRun
  termination_by
    fuel fn _args _state _result _hRun =>
      (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      (program : Program) :
      ∀ {fuel : Nat} {loopCtx : Source.Ctx}
        {cond : Expr 1} {postBase : Source.Ctx} {post : Block}
        {bodyBase : Source.Ctx} {body : Block} {state : σ}
        {outcome : Outcome σ},
        Control.Stmt.runForLoop model sourcePrim program loopCtx cond postBase post
          bodyBase body fuel state = .ok outcome →
        Control.Stmt.runForLoop model targetPrim program loopCtx cond postBase post
          bodyBase body fuel state = .ok outcome := by
    intro fuel loopCtx cond postBase post bodyBase body state outcome hRun
    cases fuel with
    | zero =>
        simp [Control.Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        unfold Control.Stmt.runForLoop at hRun ⊢
        cases hCond :
            Expr.evalCondition model sourcePrim cond state with
        | error err =>
            simp [hCond] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            have hCond' :
                Expr.evalCondition model targetPrim cond state =
                  .ok (stateAfterCond, condTrue) :=
              Locals.Source.Effectful.Expr.evalCondition_of_successRefines
                model hRefines hCond
            cases condTrue with
            | false =>
                simpa [hCond, hCond'] using hRun
            | true =>
                simp only [hCond, hCond', Bool.if_true_right]
                  at hRun ⊢
                cases hBody :
                    Control.Block.runScoped model sourcePrim program bodyBase body fuel
                      stateAfterCond with
                | error err =>
                    simp [hBody] at hRun
                | ok bodyOutcome =>
                    have hBody' :
                        Control.Block.runScoped model targetPrim program bodyBase body
                            fuel stateAfterCond =
                          .ok bodyOutcome :=
                      Block.runScoped_of_successRefines
                        model hRefines program hBody
                    cases hBodyMode : bodyOutcome.mode with
                    | brk =>
                        simpa [hBody, hBody', hBodyMode] using hRun
                    | regular =>
                        simp [hBody, hBody', hBodyMode] at hRun ⊢
                        cases hPost :
                            Control.Block.runScoped model sourcePrim program postBase
                              post fuel bodyOutcome.state with
                        | error err =>
                            simp [hPost] at hRun
                        | ok postOutcome =>
                            have hPost' :
                                Control.Block.runScoped model targetPrim program
                                    postBase post fuel bodyOutcome.state =
                                  .ok postOutcome :=
                              Block.runScoped_of_successRefines
                                model hRefines program hPost
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPost, hPost', hPostMode]
                                  at hRun ⊢
                                exact
                                  Stmt.runForLoop_of_successRefines
                                    model hRefines program hRun
                            | brk =>
                                simp [hPost, hPost', hPostMode,
                                  Source.invalid, Structured.invalid] at hRun
                            | cont =>
                                simp [hPost, hPost', hPostMode,
                                  Source.invalid, Structured.invalid] at hRun
                            | leave =>
                                simpa [hPost, hPost', hPostMode] using hRun
                            | halt kind =>
                                simpa [hPost, hPost', hPostMode] using hRun
                    | cont =>
                        simp [hBody, hBody', hBodyMode] at hRun ⊢
                        cases hPost :
                            Control.Block.runScoped model sourcePrim program postBase
                              post fuel bodyOutcome.state with
                        | error err =>
                            simp [hPost] at hRun
                        | ok postOutcome =>
                            have hPost' :
                                Control.Block.runScoped model targetPrim program
                                    postBase post fuel bodyOutcome.state =
                                  .ok postOutcome :=
                              Block.runScoped_of_successRefines
                                model hRefines program hPost
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPost, hPost', hPostMode]
                                  at hRun ⊢
                                exact
                                  Stmt.runForLoop_of_successRefines
                                    model hRefines program hRun
                            | brk =>
                                simp [hPost, hPost', hPostMode,
                                  Source.invalid, Structured.invalid] at hRun
                            | cont =>
                                simp [hPost, hPost', hPostMode,
                                  Source.invalid, Structured.invalid] at hRun
                            | leave =>
                                simpa [hPost, hPost', hPostMode] using hRun
                            | halt kind =>
                                simpa [hPost, hPost', hPostMode] using hRun
                    | leave =>
                        simpa [hBody, hBody', hBodyMode] using hRun
                    | halt kind =>
                        simpa [hBody, hBody', hBodyMode] using hRun
  termination_by
    fuel _loopCtx _cond _postBase _post _bodyBase _body _state
      _outcome _hRun => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_of_successRefines
      {σ : Type} {sourcePrim targetPrim : PrimitiveSemantics σ}
      (model : StateModel σ)
      (hRefines : sourcePrim.SuccessRefines targetPrim)
      (program : Program) :
      ∀ {fuel : Nat} {ctx : Source.Ctx} {stmt : Stmt} {state : σ}
        {outcome : Outcome σ} {runCtx : Source.Ctx},
        Control.Stmt.run model sourcePrim program ctx fuel stmt state =
          .ok (outcome, runCtx) →
        Control.Stmt.run model targetPrim program ctx fuel stmt state =
          .ok (outcome, runCtx) := by
    intro fuel ctx stmt state outcome runCtx hRun
    cases stmt with
    | expr expr =>
        unfold Control.Stmt.run at hRun ⊢
        cases hExpr : Expr.eval model sourcePrim expr state with
        | error err =>
            simp [hExpr] at hRun
        | ok result =>
            rcases result with ⟨final, values⟩
            have hExpr' :
                Expr.eval model targetPrim expr state = .ok (final, values) :=
              Locals.Source.Effectful.Expr.eval_of_successRefines
                model hRefines hExpr
            simpa [hExpr, hExpr'] using hRun
    | let_ name value =>
        unfold Control.Stmt.run at hRun ⊢
        cases hValue : Expr.evalOne model sourcePrim value state with
        | error err =>
            simp [hValue] at hRun
        | ok result =>
            rcases result with ⟨afterValue, value'⟩
            have hValue' :
                Expr.evalOne model targetPrim value state =
                  .ok (afterValue, value') :=
              Locals.Source.Effectful.Expr.evalOne_of_successRefines
                model hRefines hValue
            simpa [hValue, hValue'] using hRun
    | assign name value =>
        unfold Control.Stmt.run at hRun ⊢
        by_cases hContains : (model.vars state).contains name
        · simp only [hContains, Bool.true_eq, ↓reduceIte] at hRun ⊢
          cases hValue : Expr.evalOne model sourcePrim value state with
          | error err =>
              simp [hValue] at hRun
          | ok result =>
              rcases result with ⟨afterValue, value'⟩
              have hValue' :
                  Expr.evalOne model targetPrim value state =
                    .ok (afterValue, value') :=
                Locals.Source.Effectful.Expr.evalOne_of_successRefines
                  model hRefines hValue
              simpa [hValue, hValue'] using hRun
        · simp [hContains, Source.invalid, Structured.invalid] at hRun
    | block body =>
        unfold Control.Stmt.run at hRun ⊢
        cases hBody :
            Control.Block.runScoped model sourcePrim program ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            have hBody' :
                Control.Block.runScoped model targetPrim program ctx body fuel state =
                  .ok bodyOutcome :=
              Block.runScoped_of_successRefines model hRefines program hBody
            simpa [hBody, hBody'] using hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Control.Stmt.run at hRun ⊢
            cases hCond :
                Expr.evalCondition model sourcePrim cond state with
            | error err =>
                simp [hCond] at hRun
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                have hCond' :
                    Expr.evalCondition model targetPrim cond state =
                      .ok (stateAfterCond, condTrue) :=
                  Locals.Source.Effectful.Expr.evalCondition_of_successRefines
                    model hRefines hCond
                cases condTrue with
                | false =>
                    simpa [hCond, hCond'] using hRun
                | true =>
                    simp only [hCond, hCond', Bool.if_true_right]
                      at hRun ⊢
                    cases hBody :
                        Control.Block.runScoped model sourcePrim program ctx body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Control.Block.runScoped model targetPrim program ctx body
                                fuel stateAfterCond =
                              .ok bodyOutcome :=
                          Block.runScoped_of_successRefines
                            model hRefines program hBody
                        simpa [hBody, hBody'] using hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Control.Stmt.run at hRun ⊢
            cases hScrutinee :
                Expr.evalOne model sourcePrim scrutinee state with
            | error err =>
                simp [hScrutinee] at hRun
            | ok scrutineeResult =>
                rcases scrutineeResult with ⟨stateAfterScrutinee, value⟩
                have hScrutinee' :
                    Expr.evalOne model targetPrim scrutinee state =
                      .ok (stateAfterScrutinee, value) :=
                  Locals.Source.Effectful.Expr.evalOne_of_successRefines
                    model hRefines hScrutinee
                cases hSelected :
                    Source.Switch.select value cases defaultBody with
                | none =>
                    simpa [hScrutinee, hScrutinee', hSelected] using hRun
                | some selected =>
                    cases hBody :
                        Control.Block.runScoped model sourcePrim program ctx selected
                          fuel stateAfterScrutinee with
                    | error err =>
                        simp [hScrutinee, hSelected, hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Control.Block.runScoped model targetPrim program ctx
                                selected fuel stateAfterScrutinee =
                              .ok bodyOutcome :=
                          Block.runScoped_of_successRefines
                            model hRefines program hBody
                        simpa [hScrutinee, hScrutinee', hSelected,
                          hBody, hBody'] using hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Control.Stmt.run at hRun ⊢
            let initBase := ctx.withoutLoopControl
            cases hInit :
                Control.Block.runOpen model sourcePrim program initBase fuel init state
            with
            | error err =>
                simp [initBase, hInit] at hRun
            | ok initResult =>
                rcases initResult with ⟨initOutcome, initCtx⟩
                have hInit' :
                    Control.Block.runOpen model targetPrim program initBase fuel init
                        state =
                      .ok (initOutcome, initCtx) :=
                  Block.runOpen_of_successRefines
                    model hRefines program hInit
                cases hInitMode : initOutcome.mode with
                | regular =>
                    let loopCtx := initCtx
                    let postBase := initCtx.withoutLoopControl
                    let bodyBase :=
                      initCtx.withLoopControl initCtx.scope initCtx.scope
                    cases hLoop :
                        Control.Stmt.runForLoop model sourcePrim program loopCtx cond
                          postBase post bodyBase body fuel initOutcome.state with
                    | error err =>
                        simp [initBase, hInit, hInitMode, loopCtx,
                          postBase, bodyBase, hLoop] at hRun
                    | ok loopOutcome =>
                        have hLoop' :
                            Control.Stmt.runForLoop model targetPrim program loopCtx cond
                                postBase post bodyBase body fuel
                                initOutcome.state =
                              .ok loopOutcome :=
                          Stmt.runForLoop_of_successRefines
                            model hRefines program hLoop
                        cases hLoopMode : loopOutcome.mode with
                        | regular =>
                            simpa [initBase, hInit, hInit', hInitMode,
                              loopCtx, postBase, bodyBase, hLoop, hLoop',
                              hLoopMode] using hRun
                        | brk =>
                            simp [initBase, hInit, hInitMode, loopCtx,
                              postBase, bodyBase, hLoop, hLoopMode,
                              Source.invalid,
                              Structured.invalid] at hRun
                        | cont =>
                            simp [initBase, hInit, hInitMode, loopCtx,
                              postBase, bodyBase, hLoop, hLoopMode,
                              Source.invalid,
                              Structured.invalid] at hRun
                        | leave =>
                            simpa [initBase, hInit, hInit', hInitMode,
                              loopCtx, postBase, bodyBase, hLoop, hLoop',
                              hLoopMode] using hRun
                        | halt kind =>
                            simpa [initBase, hInit, hInit', hInitMode,
                              loopCtx, postBase, bodyBase, hLoop, hLoop',
                              hLoopMode] using hRun
                | brk =>
                    simp [initBase, hInit, hInit', hInitMode,
                      Source.invalid, Structured.invalid] at hRun
                | cont =>
                    simp [initBase, hInit, hInit', hInitMode,
                      Source.invalid, Structured.invalid] at hRun
                | leave =>
                    simpa [initBase, hInit, hInit', hInitMode] using hRun
                | halt kind =>
                    simpa [initBase, hInit, hInit', hInitMode] using hRun
    | brk =>
        simpa [Control.Stmt.run] using hRun
    | cont =>
        simpa [Control.Stmt.run] using hRun
    | leave =>
        simpa [Control.Stmt.run] using hRun
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Control.Stmt.run at hRun ⊢
            by_cases hTargets : targets.Nodup
            · simp only [hTargets, Bool.true_eq, ↓reduceIte] at hRun ⊢
              cases hArgs :
                  ArgList.Control.eval model sourcePrim args state with
              | error err =>
                  simp [hArgs] at hRun
              | ok argResult =>
                  rcases argResult with ⟨stateAfterArgs, argValues⟩
                  have hArgs' :
                      ArgList.Control.eval model targetPrim args state =
                        .ok (stateAfterArgs, argValues) :=
                    ArgList.eval_of_successRefines model hRefines hArgs
                  cases hLookup :
                      Source.FunList.find? functionName program.functions with
                  | none =>
                      simp [hArgs, hArgs', hLookup, Source.invalid,
                        Structured.invalid] at hRun
                  | some fn =>
                      cases hBody :
                          Control.FunDef.runBody model sourcePrim program fn argValues
                            fuel stateAfterArgs with
                      | error err =>
                          simp [hArgs, hArgs', hLookup, hBody] at hRun
                      | ok callResult =>
                          have hBody' :
                              Control.FunDef.runBody model targetPrim program fn
                                  argValues fuel stateAfterArgs =
                                .ok callResult :=
                            FunDef.runBody_of_successRefines
                              model hRefines program hBody
                          cases callResult with
                          | returned stateAfterCall returnValues =>
                              simpa [hArgs, hArgs', hLookup, hBody, hBody']
                                using hRun
                          | halted kind haltedState =>
                              simpa [hArgs, hArgs', hLookup, hBody, hBody']
                                using hRun
            · simp [hTargets, Source.invalid, Structured.invalid] at hRun
    | terminal kind =>
        unfold Control.Stmt.run at hRun ⊢
        cases hTerminal : sourcePrim.terminal kind state [] with
        | error err =>
            simp [hTerminal] at hRun
        | ok final =>
            have hTerminal' :
                targetPrim.terminal kind state [] = .ok final :=
              hRefines.terminal hTerminal
            simpa [hTerminal, hTerminal'] using hRun
    | terminalArgs kind args =>
        unfold Control.Stmt.run at hRun ⊢
        cases hArgs :
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
            model sourcePrim args state with
        | error err =>
            simp [hArgs] at hRun
        | ok argResult =>
            rcases argResult with ⟨afterArgs, values⟩
            have hArgs' :
                Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                    model targetPrim args state =
                  .ok (afterArgs, values) :=
              Locals.Source.Effectful.Expr.ExprSeq.eval_of_successRefines
                model hRefines hArgs
            cases hTerminal :
                sourcePrim.terminal kind afterArgs values with
            | error err =>
                simp [hArgs, hArgs', hTerminal] at hRun
            | ok final =>
                have hTerminal' :
                    targetPrim.terminal kind afterArgs values = .ok final :=
                  hRefines.terminal hTerminal
                simpa [hArgs, hArgs', hTerminal, hTerminal'] using hRun
  termination_by
    fuel _ctx stmt _state _outcome _runCtx _hRun =>
      (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace FunDef

def bodyCtx (fn : Functions.FunDef) : Source.Ctx :=
  let functionScope := fn.returns ++ fn.params
  { Source.Ctx.initial.withLeaveScope functionScope with
    scope := functionScope }

theorem runBody_returned_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {fn : Functions.FunDef} {args : List Word}
    {fuel : Nat} {state returnedState : σ}
    {returnValues : List Word}
    (hRun :
      Control.FunDef.runBody model prim program fn args (fuel + 1) state =
        .ok (CallResult.returned returnedState returnValues)) :
    ∃ paramStore bodyOutcome bodyCtx',
      Source.Store.insertMany fn.params args Locals.Source.Store.empty =
        some paramStore ∧
      Control.Block.runOpen model prim program (bodyCtx fn) fuel fn.body
          (model.withSource state
            { shared := (model.source state).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (bodyOutcome, bodyCtx') ∧
      (bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave) ∧
      Source.Store.lookupMany fn.returns (model.vars bodyOutcome.state) =
        some returnValues ∧
      bodyOutcome.state = returnedState := by
  unfold Control.FunDef.runBody at hRun
  cases hParams :
      Source.Store.insertMany fn.params args Locals.Source.Store.empty with
  | none =>
      simp [hParams, Source.invalid, Structured.invalid] at hRun
  | some paramStore =>
      simp [hParams] at hRun
      cases hBody :
          Control.Block.runOpen model prim program
            { Source.Ctx.withLeaveScope Source.Ctx.initial
                (fn.returns ++ fn.params) with
              scope := fn.returns ++ fn.params }
            fuel fn.body
            (model.withSource state
              { shared := (model.source state).shared,
                vars := Source.Store.initReturns fn.returns paramStore }) with
      | error err =>
          simp [hBody] at hRun
      | ok bodyResult =>
          rcases bodyResult with ⟨bodyOutcome, bodyCtx'⟩
          simp [hBody] at hRun
          cases hMode : bodyOutcome.mode with
          | regular =>
              simp [hMode] at hRun
              cases hLookup :
                  Source.Store.lookupMany fn.returns
                    (model.vars bodyOutcome.state) with
              | none =>
                  simp [hLookup, Source.invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
                  rcases hRun with ⟨hState, hValues⟩
                  subst returnedState
                  subst values
                  exact
                    ⟨paramStore, bodyOutcome, bodyCtx', rfl,
                      by simpa [bodyCtx] using hBody,
                      Or.inl hMode, hLookup, rfl⟩
          | leave =>
              simp [hMode] at hRun
              cases hLookup :
                  Source.Store.lookupMany fn.returns
                    (model.vars bodyOutcome.state) with
              | none =>
                  simp [hLookup, Source.invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
                  rcases hRun with ⟨hState, hValues⟩
                  subst returnedState
                  subst values
                  exact
                    ⟨paramStore, bodyOutcome, bodyCtx', rfl,
                      by simpa [bodyCtx] using hBody,
                      Or.inr hMode, hLookup, rfl⟩
          | brk =>
              simp [hMode, Source.invalid, Structured.invalid] at hRun
          | cont =>
              simp [hMode, Source.invalid, Structured.invalid] at hRun
          | halt kind =>
              simp [hMode] at hRun

theorem runBody_returned_of_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {fn : Functions.FunDef} {args : List Word}
    {fuel : Nat} {state returnedState : σ}
    {returnValues : List Word}
    {paramStore : Source.Store}
    {bodyOutcome : Outcome σ} {bodyCtx' : Source.Ctx}
    (hParams :
      Source.Store.insertMany fn.params args Locals.Source.Store.empty =
        some paramStore)
    (hBody :
      Control.Block.runOpen model prim program (bodyCtx fn) fuel fn.body
          (model.withSource state
            { shared := (model.source state).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (bodyOutcome, bodyCtx'))
    (hMode : bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave)
    (hReturns :
      Source.Store.lookupMany fn.returns (model.vars bodyOutcome.state) =
        some returnValues)
    (hState : bodyOutcome.state = returnedState) :
    Control.FunDef.runBody model prim program fn args (fuel + 1) state =
      .ok (CallResult.returned returnedState returnValues) := by
  have hBody' :
      Control.Block.runOpen model prim program
          { Source.Ctx.withLeaveScope Source.Ctx.initial
              (fn.returns ++ fn.params) with
            scope := fn.returns ++ fn.params }
          fuel fn.body
          (model.withSource state
            { shared := (model.source state).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (bodyOutcome, bodyCtx') := by
    simpa [bodyCtx] using hBody
  have hReturns' :
      Source.Store.lookupMany fn.returns (model.vars returnedState) =
        some returnValues := by
    simpa [← hState] using hReturns
  rcases hMode with hMode | hMode
  · simp [Control.FunDef.runBody, hParams, hBody', hMode, hReturns', hState]
  · simp [Control.FunDef.runBody, hParams, hBody', hMode, hReturns', hState]

/--
Construct a canonical halting function-body result from the actual parameter
initialization and open body execution. Return lookup and caller restoration
are unreachable after a halt.
-/
theorem runBody_halted_of_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {fn : Functions.FunDef} {args : List Word}
    {fuel : Nat} {state haltedState : σ}
    {kind : Assembly.HaltKind}
    {paramStore : Source.Store} {bodyCtx' : Source.Ctx}
    (hParams :
      Source.Store.insertMany fn.params args Locals.Source.Store.empty =
        some paramStore)
    (hBody :
      Control.Block.runOpen model prim program (bodyCtx fn) fuel fn.body
          (model.withSource state
            { shared := (model.source state).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (Outcome.halt kind haltedState, bodyCtx')) :
    Control.FunDef.runBody model prim program fn args (fuel + 1) state =
      .ok (CallResult.halted kind haltedState) := by
  have hBody' :
      Control.Block.runOpen model prim program
          { Source.Ctx.withLeaveScope Source.Ctx.initial
              (fn.returns ++ fn.params) with
            scope := fn.returns ++ fn.params }
          fuel fn.body
          (model.withSource state
            { shared := (model.source state).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (Outcome.halt kind haltedState, bodyCtx') := by
    simpa [bodyCtx] using hBody
  simp [Control.FunDef.runBody, hParams, hBody', Outcome.halt,
    Locals.Source.Effectful.Outcome.halt]

theorem runBody_halted_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {fn : Functions.FunDef} {args : List Word}
    {fuel : Nat} {state haltedState : σ}
    {kind : Assembly.HaltKind}
    (hRun :
      Control.FunDef.runBody model prim program fn args (fuel + 1) state =
        .ok (CallResult.halted kind haltedState)) :
    ∃ paramStore bodyCtx',
      Source.Store.insertMany fn.params args Locals.Source.Store.empty =
        some paramStore ∧
      Control.Block.runOpen model prim program (bodyCtx fn) fuel fn.body
          (model.withSource state
            { shared := (model.source state).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (Outcome.halt kind haltedState, bodyCtx') := by
  unfold Control.FunDef.runBody at hRun
  cases hParams :
      Source.Store.insertMany fn.params args Locals.Source.Store.empty with
  | none =>
      simp [hParams, Source.invalid, Structured.invalid] at hRun
  | some paramStore =>
      simp [hParams] at hRun
      cases hBody :
          Control.Block.runOpen model prim program
            { Source.Ctx.withLeaveScope Source.Ctx.initial
                (fn.returns ++ fn.params) with
              scope := fn.returns ++ fn.params }
            fuel fn.body
            (model.withSource state
              { shared := (model.source state).shared,
                vars := Source.Store.initReturns fn.returns paramStore }) with
      | error err =>
          simp [hBody] at hRun
      | ok bodyResult =>
          rcases bodyResult with ⟨bodyOutcome, bodyCtx'⟩
          simp [hBody] at hRun
          cases hMode : bodyOutcome.mode with
          | regular =>
              simp [hMode] at hRun
              cases hLookup :
                  Source.Store.lookupMany fn.returns
                    (model.vars bodyOutcome.state) with
              | none =>
                  simp [hLookup, Source.invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
          | leave =>
              simp [hMode] at hRun
              cases hLookup :
                  Source.Store.lookupMany fn.returns
                    (model.vars bodyOutcome.state) with
              | none =>
                  simp [hLookup, Source.invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
          | brk =>
              simp [hMode, Source.invalid, Structured.invalid] at hRun
          | cont =>
              simp [hMode, Source.invalid, Structured.invalid] at hRun
          | halt actualKind =>
              rcases bodyOutcome with ⟨bodyState, bodyMode⟩
              simp at hMode
              subst bodyMode
              simp at hRun
              rcases hRun with ⟨hKind, hState⟩
              subst actualKind
              subst haltedState
              exact
                ⟨paramStore, bodyCtx', rfl,
                  by simpa [bodyCtx, Outcome.halt] using hBody⟩

theorem runBody_args_length {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {fn : Functions.FunDef} {args : List Word}
    {fuel : Nat} {state : σ} {result : CallResult σ}
    (hRun :
      Control.FunDef.runBody model prim program fn args fuel state = .ok result) :
    args.length = fn.params.length := by
  cases fuel with
  | zero =>
      simp [Control.FunDef.runBody, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold Control.FunDef.runBody at hRun
      cases hParams :
          Source.Store.insertMany fn.params args Locals.Source.Store.empty with
      | none =>
          simp [hParams, Source.invalid, Structured.invalid] at hRun
      | some paramStore =>
          exact Source.Store.insertMany_length hParams

theorem runBody_returned_length {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {fn : Functions.FunDef} {args values : List Word}
    {fuel : Nat} {state returnedState : σ}
    (hRun :
      Control.FunDef.runBody model prim program fn args fuel state =
        .ok (CallResult.returned returnedState values)) :
    values.length = fn.returns.length := by
  cases fuel with
  | zero =>
      simp [Control.FunDef.runBody, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      rcases runBody_returned_parts model prim program hRun with
        ⟨_paramStore, bodyOutcome, _bodyCtx, _hParams, _hBody, _hMode,
          hLookup, _hState⟩
      exact Source.Store.lookupMany_length hLookup

end FunDef

namespace Stmt

/--
A literal-valued declaration is effect-free and extends the current scope.
-/
theorem run_let_lit {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat} {state : σ}
    (name : Name) (value : Word) :
    Control.Stmt.run model prim program ctx fuel (.let_ name (.lit value)) state =
      .ok
        (Outcome.regular (model.insert state name value),
          { ctx with scope := name :: ctx.scope }) := by
  simp [Control.Stmt.run, Expr.evalOne, Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.Control.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.Control.eval]

theorem run_let_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat} {state stateAfterValue : σ}
    {name : Name} {value : Functions.Expr 1} {result : Word}
    (hEval :
      Expr.evalOne model prim value state =
        .ok (stateAfterValue, result)) :
    Control.Stmt.run model prim program ctx fuel (.let_ name value) state =
      .ok
        (Outcome.regular (model.insert stateAfterValue name result),
          { ctx with scope := name :: ctx.scope }) := by
  simp [Control.Stmt.run, hEval]

theorem run_assign_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat} {state stateAfterValue : σ}
    {name : Name} {value : Functions.Expr 1} {result : Word}
    (hContains : (model.vars state).contains name = true)
    (hEval :
      Expr.evalOne model prim value state =
        .ok (stateAfterValue, result)) :
    Control.Stmt.run model prim program ctx fuel (.assign name value) state =
      .ok
        (Outcome.regular
          (model.withVars stateAfterValue
            (Locals.Source.Store.insert
              (model.vars stateAfterValue) name result)),
          ctx) := by
  simp [Control.Stmt.run, hContains, hEval]

/--
A successful `leave` statement has leave mode.
-/
theorem run_leave_mode {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx fuel .leave source =
        .ok (outcome, finalCtx)) :
    outcome.mode = .leave := by
  unfold Control.Stmt.run at hRun
  cases hScope : ctx.leaveScope? with
  | none =>
      simp [hScope, Source.invalid, Structured.invalid] at hRun
  | some scope =>
      simp only [hScope] at hRun
      have hEq := (Except.ok.inj hRun).symm
      exact congrArg (fun result => result.1.mode) hEq

theorem run_leave_of_scope {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat} {state : σ}
    {scope : List Name}
    (hScope : ctx.leaveScope? = some scope) :
    Control.Stmt.run model prim program ctx fuel .leave state =
      .ok (Outcome.leave (model.restrictTo scope state), ctx) := by
  simp [Control.Stmt.run, hScope]

theorem run_brk_of_scope {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat} {state : σ}
    {scope : List Name}
    (hScope : ctx.breakScope? = some scope) :
    Control.Stmt.run model prim program ctx fuel .brk state =
      .ok (Outcome.brk (model.restrictTo scope state), ctx) := by
  simp [Control.Stmt.run, hScope]

theorem run_cont_of_scope {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat} {state : σ}
    {scope : List Name}
    (hScope : ctx.continueScope? = some scope) :
    Control.Stmt.run model prim program ctx fuel .cont state =
      .ok (Outcome.cont (model.restrictTo scope state), ctx) := by
  simp [Control.Stmt.run, hScope]

/--
A successful plain terminal statement has the requested halt mode.
-/
theorem run_terminal_mode {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {kind : Assembly.HaltKind}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx fuel (.terminal kind) source =
        .ok (outcome, finalCtx)) :
    outcome.mode = .halt kind := by
  unfold Control.Stmt.run at hRun
  cases hTerminal : prim.terminal kind source [] with
  | error err =>
      simp [hTerminal] at hRun
  | ok sourceFinal =>
      simp only [hTerminal] at hRun
      have hEq := (Except.ok.inj hRun).symm
      exact congrArg (fun result => result.1.mode) hEq

/--
A successful terminal-with-arguments statement has the requested halt mode.
-/
theorem run_terminalArgs_mode {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx fuel (.terminalArgs kind args) source =
        .ok (outcome, finalCtx)) :
    outcome.mode = .halt kind := by
  unfold Control.Stmt.run at hRun
  cases hArgs :
      Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        model prim args source with
  | error err =>
      simp [hArgs] at hRun
  | ok result =>
      rcases result with ⟨afterArgs, values⟩
      simp only [hArgs, Bind.bind, Except.bind] at hRun
      cases hTerminal : prim.terminal kind afterArgs values with
      | error err =>
          simp [hTerminal] at hRun
      | ok sourceFinal =>
          simp only [hTerminal] at hRun
          have hEq := (Except.ok.inj hRun).symm
          exact congrArg (fun result => result.1.mode) hEq

theorem run_terminalArgs_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx fuel
          (.terminalArgs kind args) source =
        .ok (outcome, finalCtx)) :
    ∃ stateAfterArgs values final,
      Locals.Source.Effectful.Expr.Control.ExprSeq.eval
          model prim args source =
        .ok (stateAfterArgs, values) ∧
      prim.terminal kind stateAfterArgs values = .ok final ∧
      outcome = Outcome.halt kind final ∧
      finalCtx = ctx := by
  unfold Control.Stmt.run at hRun
  cases hArgs :
      Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        model prim args source with
  | error err =>
      simp [hArgs] at hRun
  | ok result =>
      rcases result with ⟨stateAfterArgs, values⟩
      simp only [hArgs, Bind.bind, Except.bind] at hRun
      cases hTerminal : prim.terminal kind stateAfterArgs values with
      | error err =>
          simp [hTerminal] at hRun
      | ok final =>
          simp only [hTerminal] at hRun
          have hEq := Except.ok.inj hRun
          exact
            ⟨stateAfterArgs, values, final, rfl, hTerminal,
              (congrArg Prod.fst hEq).symm,
              (congrArg Prod.snd hEq).symm⟩

/--
A successful call statement either returns regularly or propagates a terminal
callee outcome. Its source context is unchanged in both cases.
-/
theorem run_call_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 1)
          (.call targets functionName args) source =
        .ok (outcome, finalCtx)) :
    (∃ sourceFinal,
        outcome = Outcome.regular sourceFinal ∧ finalCtx = ctx) ∨
      (∃ kind sourceFinal,
        outcome = Outcome.halt kind sourceFinal ∧ finalCtx = ctx) := by
  unfold Control.Stmt.run at hRun
  by_cases hTargets : targets.Nodup
  · simp only [hTargets, ↓reduceIte] at hRun
    cases hArgs : ArgList.Control.eval model prim args source with
    | error err =>
        simp [hArgs] at hRun
    | ok argResult =>
        rcases argResult with ⟨stateAfterArgs, argValues⟩
        simp [hArgs] at hRun
        cases hFind :
            Source.FunList.find? functionName program.functions with
        | none =>
            simp [hFind, Source.invalid, Structured.invalid] at hRun
        | some fn =>
            simp [hFind] at hRun
            cases hBody :
                Control.FunDef.runBody model prim program fn argValues fuel
                  stateAfterArgs with
            | error err =>
                simp [hBody] at hRun
            | ok callResult =>
                cases callResult with
                | returned stateAfterCall returnValues =>
                    simp [hBody] at hRun
                    cases hAssign :
                        Source.Store.assignMany targets returnValues
                          (model.vars stateAfterArgs) with
                    | none =>
                        simp [hAssign, Source.invalid, Structured.invalid]
                          at hRun
                    | some returnStore =>
                        simp only [hAssign] at hRun
                        have hEq := (Except.ok.inj hRun).symm
                        left
                        exact
                          ⟨model.withSource stateAfterCall
                              { shared := (model.source stateAfterCall).shared
                                vars := returnStore },
                            congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
                | halted kind haltedState =>
                    simp [hBody] at hRun
                    right
                    exact
                      ⟨kind, haltedState, hRun.1.symm, hRun.2.symm⟩
  · simp [hTargets, Source.invalid, Structured.invalid] at hRun

theorem call_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source sourceAfter : σ}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 1)
          (.call targets functionName args) source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    ∃ stateAfterArgs argValues fn stateAfterCall returnValues returnStore,
      targets.Nodup ∧
      ArgList.Control.eval model prim args source =
        .ok (stateAfterArgs, argValues) ∧
      Source.FunList.find? functionName program.functions = some fn ∧
      Control.FunDef.runBody model prim program fn argValues fuel stateAfterArgs =
        .ok (CallResult.returned stateAfterCall returnValues) ∧
      Source.Store.assignMany targets returnValues
          (model.vars stateAfterArgs) =
        some returnStore ∧
      sourceAfter =
        model.withSource stateAfterCall
          { shared := (model.source stateAfterCall).shared,
            vars := returnStore } := by
  unfold Control.Stmt.run at hRun
  by_cases hTargets : targets.Nodup
  · simp [hTargets] at hRun
    cases hArgs : ArgList.Control.eval model prim args source with
    | error err =>
        simp [hArgs] at hRun
    | ok argResult =>
        rcases argResult with ⟨stateAfterArgs, argValues⟩
        simp [hArgs] at hRun
        cases hFind :
            Source.FunList.find? functionName program.functions with
        | none =>
            simp [hFind, Source.invalid, Structured.invalid] at hRun
        | some fn =>
            simp [hFind] at hRun
            cases hBody :
                Control.FunDef.runBody model prim program fn argValues fuel
                  stateAfterArgs with
            | error err =>
                simp [hBody] at hRun
            | ok callResult =>
                cases callResult with
                | returned stateAfterCall returnValues =>
                    simp [hBody] at hRun
                    cases hAssign :
                        Source.Store.assignMany targets returnValues
                          (model.vars stateAfterArgs) with
                    | none =>
                        simp [hAssign, Source.invalid, Structured.invalid]
                          at hRun
                    | some returnStore =>
                        simp [hAssign] at hRun
                        cases hRun
                        exact
                          ⟨stateAfterArgs, argValues, fn, stateAfterCall,
                            returnValues, returnStore, hTargets,
                            by simpa [hArgs], by simpa [hFind],
                            by simpa [hBody], by simpa [hAssign], rfl⟩
                | halted kind haltedState =>
                    simp [hBody, Outcome.regular, Outcome.halt] at hRun
                    cases hRun
  · simp [hTargets, Source.invalid, Structured.invalid] at hRun

theorem call_regular_of_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source stateAfterArgs stateAfterCall sourceAfter : σ}
    {argValues returnValues : List Word}
    {fn : Functions.FunDef} {returnStore : Source.Store}
    (hTargets : targets.Nodup)
    (hArgs :
      ArgList.Control.eval model prim args source =
        .ok (stateAfterArgs, argValues))
    (hFind :
      Source.FunList.find? functionName program.functions = some fn)
    (hCall :
      Control.FunDef.runBody model prim program fn argValues fuel stateAfterArgs =
        .ok (CallResult.returned stateAfterCall returnValues))
    (hAssign :
      Source.Store.assignMany targets returnValues
          (model.vars stateAfterArgs) =
        some returnStore)
    (hFinal :
      sourceAfter =
        model.withSource stateAfterCall
          { shared := (model.source stateAfterCall).shared,
            vars := returnStore }) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.call targets functionName args) source =
      .ok (Outcome.regular sourceAfter, ctx) := by
  subst sourceAfter
  simp [Control.Stmt.run, hTargets, hArgs, hFind, hCall, hAssign]

/--
A regular call with two available fuel steps exposes the strictly smaller
callee-body execution used by recursive preservation proofs.
-/
theorem call_regular_body_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source sourceAfter : σ}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 2)
          (.call targets functionName args) source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    ∃ stateAfterArgs argValues fn stateAfterCall returnValues returnStore
        paramStore bodyOutcome bodyCtx',
      targets.Nodup ∧
      ArgList.Control.eval model prim args source =
        .ok (stateAfterArgs, argValues) ∧
      Source.FunList.find? functionName program.functions = some fn ∧
      Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore ∧
      Control.Block.runOpen model prim program (FunDef.bodyCtx fn) fuel fn.body
          (model.withSource stateAfterArgs
            { shared := (model.source stateAfterArgs).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (bodyOutcome, bodyCtx') ∧
      (bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave) ∧
      Source.Store.lookupMany fn.returns
          (model.vars bodyOutcome.state) =
        some returnValues ∧
      bodyOutcome.state = stateAfterCall ∧
      Source.Store.assignMany targets returnValues
          (model.vars stateAfterArgs) =
        some returnStore ∧
      sourceAfter =
        model.withSource stateAfterCall
          { shared := (model.source stateAfterCall).shared,
            vars := returnStore } := by
  obtain
      ⟨stateAfterArgs, argValues, fn, stateAfterCall,
        returnValues, returnStore, hTargets, hArgs, hFind,
        hCall, hAssign, hFinal⟩ :=
    call_regular_parts model prim program
      (fuel := fuel + 1) (by simpa [Nat.add_assoc] using hRun)
  obtain
      ⟨paramStore, bodyOutcome, bodyCtx',
        hParams, hBody, hMode, hReturns, hState⟩ :=
    FunDef.runBody_returned_parts model prim program hCall
  exact
    ⟨stateAfterArgs, argValues, fn, stateAfterCall,
      returnValues, returnStore, paramStore, bodyOutcome, bodyCtx',
      hTargets, hArgs, hFind, hParams, hBody, hMode, hReturns,
      hState, hAssign, hFinal⟩

/--
Construct a canonical halting call statement from successful argument
evaluation, compiler-selected function lookup, and a halting function body.
Target assignment and caller-local restoration are unreachable after a halt.
-/
theorem call_halted_of_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source stateAfterArgs haltedState : σ}
    {argValues : List Word} {fn : Functions.FunDef}
    {kind : Assembly.HaltKind}
    (hTargets : targets.Nodup)
    (hArgs :
      ArgList.Control.eval model prim args source =
        .ok (stateAfterArgs, argValues))
    (hFind :
      Source.FunList.find? functionName program.functions = some fn)
    (hBody :
      Control.FunDef.runBody model prim program fn argValues fuel stateAfterArgs =
        .ok (CallResult.halted kind haltedState)) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.call targets functionName args) source =
      .ok (Outcome.halt kind haltedState, ctx) := by
  simp [Control.Stmt.run, hTargets, hArgs, hFind, hBody, Outcome.halt]

theorem call_halted_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source haltedState : σ} {kind : Assembly.HaltKind}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 1)
          (.call targets functionName args) source =
        .ok (Outcome.halt kind haltedState, ctx)) :
    ∃ stateAfterArgs argValues fn,
      targets.Nodup ∧
      ArgList.Control.eval model prim args source =
        .ok (stateAfterArgs, argValues) ∧
      Source.FunList.find? functionName program.functions = some fn ∧
      Control.FunDef.runBody model prim program fn argValues fuel stateAfterArgs =
        .ok (CallResult.halted kind haltedState) := by
  unfold Control.Stmt.run at hRun
  by_cases hTargets : targets.Nodup
  · simp [hTargets] at hRun
    cases hArgs : ArgList.Control.eval model prim args source with
    | error err =>
        simp [hArgs] at hRun
    | ok argResult =>
        rcases argResult with ⟨stateAfterArgs, argValues⟩
        simp [hArgs] at hRun
        cases hFind :
            Source.FunList.find? functionName program.functions with
        | none =>
            simp [hFind, Source.invalid, Structured.invalid] at hRun
        | some fn =>
            simp [hFind] at hRun
            cases hBody :
                Control.FunDef.runBody model prim program fn argValues fuel
                  stateAfterArgs with
            | error err =>
                simp [hBody] at hRun
            | ok callResult =>
                cases callResult with
                | returned stateAfterCall returnValues =>
                    simp [hBody] at hRun
                    cases hAssign :
                        Source.Store.assignMany targets returnValues
                          (model.vars stateAfterArgs) with
                    | none =>
                        simp [hAssign, Source.invalid, Structured.invalid]
                          at hRun
                    | some returnStore =>
                        simp [hAssign, Outcome.regular, Outcome.halt] at hRun
                        cases hRun
                | halted actualKind actualState =>
                    simp [hBody, Outcome.halt] at hRun
                    cases hRun
                    exact
                      ⟨stateAfterArgs, argValues, fn, hTargets,
                        by simpa [hArgs], by simpa [hFind],
                        by simpa [hBody]⟩
  · simp [hTargets, Source.invalid, Structured.invalid] at hRun

/--
Expose the exact selected body run behind a halting call statement.

This is the call analogue of `call_regular_body_parts`: the statement-level
fuel pays for call dispatch and `runBody`, leaving the strictly smaller body
fuel for recursive preservation.
-/
theorem call_halted_body_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name}
    {args : List (Functions.Expr 1)}
    {source haltedState : σ} {kind : Assembly.HaltKind}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 2)
          (.call targets functionName args) source =
        .ok (Outcome.halt kind haltedState, ctx)) :
    ∃ stateAfterArgs argValues fn paramStore bodyCtx',
      targets.Nodup ∧
      ArgList.Control.eval model prim args source =
        .ok (stateAfterArgs, argValues) ∧
      Source.FunList.find? functionName program.functions = some fn ∧
      Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore ∧
      Control.Block.runOpen model prim program (FunDef.bodyCtx fn) fuel fn.body
          (model.withSource stateAfterArgs
            { shared := (model.source stateAfterArgs).shared,
              vars := Source.Store.initReturns fn.returns paramStore }) =
        .ok (Outcome.halt kind haltedState, bodyCtx') := by
  obtain
      ⟨stateAfterArgs, argValues, fn, hTargets, hArgs, hFind, hBody⟩ :=
    call_halted_parts model prim program
      (fuel := fuel + 1) (by simpa [Nat.add_assoc] using hRun)
  obtain ⟨paramStore, bodyCtx', hParams, hBodyRun⟩ :=
    FunDef.runBody_halted_parts model prim program hBody
  exact
    ⟨stateAfterArgs, argValues, fn, paramStore, bodyCtx',
      hTargets, hArgs, hFind, hParams, hBodyRun⟩

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
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok
        (Outcome.regular
          (model.restrictTo loopCtx.scope afterCond)) := by
  simp [Control.Stmt.runForLoop, hCond, Outcome.regular,
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          (fuel + 1) init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hCond :
      Expr.evalCondition model prim cond afterInit =
        .ok (afterCond, false)) :
    Control.Stmt.run model prim program ctx (fuel + 2)
        (.for_ init cond post body) source =
      .ok
        (Outcome.regular
          (model.restrictTo ctx.scope
            (model.restrictTo initCtx.scope afterCond)),
          ctx) := by
  simp [Control.Stmt.run, hInit, Control.Stmt.runForLoop, hCond, Outcome.regular,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
      .ok (Outcome.brk afterBody)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.regular afterBody) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, Outcome.brk,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.leave afterBody)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.leave afterBody) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, Outcome.leave,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.halt kind afterBody)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.halt kind afterBody) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, Outcome.halt,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok (Outcome.regular final)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.regular final) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, hLoop, Outcome.regular,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok (Outcome.regular final)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.regular final) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, hLoop,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok outcome) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok outcome := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, hLoop, Outcome.regular,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.regular afterPost))
    (hLoop :
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel afterPost =
        .ok outcome) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok outcome := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, hLoop,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.leave afterPost)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.leave afterPost) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, Outcome.regular,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.leave afterPost)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.leave afterPost) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, Outcome.cont,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.regular afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.halt kind afterPost)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.halt kind afterPost) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, Outcome.regular,
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
      Control.Block.runScoped model prim program bodyBase body fuel afterCond =
        .ok (Outcome.cont afterBody))
    (hPost :
      Control.Block.runScoped model prim program postBase post fuel afterBody =
        .ok (Outcome.halt kind afterPost)) :
    Control.Stmt.runForLoop model prim program loopCtx cond postBase post
        bodyBase body (fuel + 1) source =
      .ok (Outcome.halt kind afterPost) := by
  simp [Control.Stmt.runForLoop, hCond, hBody, hPost, Outcome.cont,
    Locals.Source.Effectful.Outcome.cont, Outcome.halt,
    Locals.Source.Effectful.Outcome.halt]

/--
Every successful canonical loop result is either regular or exits the current
activation. Loop-local break and continue outcomes are consumed internally.
-/
theorem runForLoop_regular_or_exit {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {loopCtx : Source.Ctx} {cond : Functions.Expr 1}
    {postBase : Source.Ctx} {post : Functions.Block}
    {bodyBase : Source.Ctx} {body : Functions.Block} :
    ∀ {fuel : Nat} {source : σ} {outcome : Outcome σ},
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel source =
        .ok outcome →
      outcome.mode = .regular ∨ outcome.IsExit := by
  intro fuel
  induction fuel with
  | zero =>
      intro source outcome hRun
      simp [Control.Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
  | succ fuel ih =>
      intro source outcome hRun
      rw [Control.Stmt.runForLoop] at hRun
      cases hCond : Expr.evalCondition model prim cond source with
      | error err =>
          simp [hCond] at hRun
      | ok condResult =>
          rcases condResult with ⟨afterCond, condTrue⟩
          cases condTrue with
          | false =>
              simp [hCond] at hRun
              subst outcome
              exact .inl rfl
          | true =>
              cases hBody :
                  Control.Block.runScoped model prim program bodyBase body fuel
                    afterCond with
              | error err =>
                  simp [hCond, hBody] at hRun
              | ok bodyOutcome =>
                  rcases bodyOutcome with ⟨afterBody, bodyMode⟩
                  cases bodyMode with
                  | regular =>
                      cases hPost :
                          Control.Block.runScoped model prim program postBase post
                            fuel afterBody with
                      | error err =>
                          simp [hCond, hBody, hPost] at hRun
                      | ok postOutcome =>
                          rcases postOutcome with ⟨afterPost, postMode⟩
                          cases postMode with
                          | regular =>
                              simp [hCond, hBody, hPost] at hRun
                              exact ih hRun
                          | brk =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | cont =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | leave =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              exact .inr (by simp [Outcome.IsExit])
                          | halt kind =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              exact .inr (by simp [Outcome.IsExit])
                  | brk =>
                      simp [hCond, hBody] at hRun
                      subst outcome
                      exact .inl rfl
                  | cont =>
                      cases hPost :
                          Control.Block.runScoped model prim program postBase post
                            fuel afterBody with
                      | error err =>
                          simp [hCond, hBody, hPost] at hRun
                      | ok postOutcome =>
                          rcases postOutcome with ⟨afterPost, postMode⟩
                          cases postMode with
                          | regular =>
                              simp [hCond, hBody, hPost] at hRun
                              exact ih hRun
                          | brk =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | cont =>
                              simp [hCond, hBody, hPost, Source.invalid,
                                Structured.invalid] at hRun
                          | leave =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              exact .inr (by simp [Outcome.IsExit])
                          | halt kind =>
                              simp [hCond, hBody, hPost] at hRun
                              subst outcome
                              exact .inr (by simp [Outcome.IsExit])
                  | leave =>
                      simp [hCond, hBody] at hRun
                      subst outcome
                      exact .inr (by simp [Outcome.IsExit])
                  | halt kind =>
                      simp [hCond, hBody] at hRun
                      subst outcome
                      exact .inr (by simp [Outcome.IsExit])

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
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
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
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.brk afterBody) ∧
            final = afterBody) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.regular afterBody) ∧
            Control.Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Control.Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok (Outcome.regular final)) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.cont afterBody) ∧
            Control.Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Control.Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok (Outcome.regular final))) := by
  cases fuel with
  | zero =>
      simp [Control.Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
  | succ stepFuel =>
      refine ⟨stepFuel, rfl, ?_⟩
      rw [Control.Stmt.runForLoop] at hRun
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
                  Control.Block.runScoped model prim program bodyBase body stepFuel
                    afterCond with
              | error err =>
                  simp [hCond, hBody] at hRun
              | ok bodyOutcome =>
                  rcases bodyOutcome with ⟨afterBody, bodyMode⟩
                  cases bodyMode with
                  | regular =>
                      cases hPost :
                          Control.Block.runScoped model prim program postBase post
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
                          Control.Block.runScoped model prim program postBase post
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
      Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel source =
        .ok outcome) :
    ∃ stepFuel, fuel = stepFuel + 1 ∧
      ((∃ afterCond,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok outcome) ∨
        (∃ afterCond afterBody,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.regular afterBody) ∧
            Control.Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok outcome) ∨
        (∃ afterCond afterBody,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.cont afterBody) ∧
            Control.Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok outcome) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.regular afterBody) ∧
            Control.Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Control.Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok outcome) ∨
        (∃ afterCond afterBody afterPost,
          Expr.evalCondition model prim cond source =
              .ok (afterCond, true) ∧
            Control.Block.runScoped model prim program bodyBase body stepFuel
                afterCond =
              .ok (Outcome.cont afterBody) ∧
            Control.Block.runScoped model prim program postBase post stepFuel
                afterBody =
              .ok (Outcome.regular afterPost) ∧
            Control.Stmt.runForLoop model prim program loopCtx cond postBase post
                bodyBase body stepFuel afterPost =
              .ok outcome)) := by
  cases fuel with
  | zero =>
      simp [Control.Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
  | succ stepFuel =>
      refine ⟨stepFuel, rfl, ?_⟩
      rw [Control.Stmt.runForLoop] at hRun
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
                  Control.Block.runScoped model prim program bodyBase body stepFuel
                    afterCond with
              | error err =>
                  simp [hCond, hBody] at hRun
              | ok bodyOutcome =>
                  rcases bodyOutcome with ⟨afterBody, bodyMode⟩
                  cases bodyMode with
                  | regular =>
                      cases hPost :
                          Control.Block.runScoped model prim program postBase post
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
                          Control.Block.runScoped model prim program postBase post
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          (fuel + 1) init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hCond :
      Expr.evalCondition model prim cond afterInit =
        .ok (afterCond, true))
    (hBody :
      Control.Block.runScoped model prim program
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterCond =
        .ok (Outcome.brk afterBody)) :
    Control.Stmt.run model prim program ctx (fuel + 2)
        (.for_ init cond post body) source =
      .ok
        (Outcome.regular (model.restrictTo ctx.scope afterBody),
          ctx) := by
  simp [Control.Stmt.run, hInit, Control.Stmt.runForLoop, hCond, hBody,
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Control.Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok (Outcome.regular final)) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok
        (Outcome.regular (model.restrictTo ctx.scope final),
          ctx) := by
  simp [Control.Stmt.run, hInit, hLoop, Outcome.regular,
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Control.Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok (Outcome.leave final)) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok (Outcome.leave final, ctx) := by
  simp [Control.Stmt.run, hInit, hLoop, Outcome.regular,
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Control.Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok (Outcome.halt kind final)) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.for_ init cond post body) source =
      .ok (Outcome.halt kind final, ctx) := by
  simp [Control.Stmt.run, hInit, hLoop, Outcome.regular,
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (Outcome.regular afterInit, initCtx))
    (hLoop :
      Control.Stmt.runForLoop model prim program initCtx cond
          initCtx.withoutLoopControl post
          (initCtx.withLoopControl initCtx.scope initCtx.scope)
          body fuel afterInit =
        .ok outcome) :
    Control.Stmt.run model prim program ctx (fuel + 1)
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
      Control.Block.runOpen model prim program ctx.withoutLoopControl
          fuel init source =
        .ok (outcome, initCtx)) :
    Control.Stmt.run model prim program ctx (fuel + 1)
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
      rw [Control.Stmt.run, hInit]
      rfl
  | halt kind =>
      rw [Control.Stmt.run, hInit]
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
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.if_ cond body) source =
      .ok (Outcome.regular afterCond, ctx) := by
  simp [Control.Stmt.run, hCond, Outcome.regular,
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
      Control.Block.runScoped model prim program ctx body fuel afterCond =
        .ok outcome) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.if_ cond body) source =
      .ok (outcome, ctx) := by
  simp [Control.Stmt.run, hCond, hBody]

/--
Invert a successful canonical source `if` at its exact smaller body fuel.
-/
theorem run_if_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 1)
          (.if_ cond body) source =
        .ok (outcome, finalCtx)) :
    (∃ afterCond,
        Expr.evalCondition model prim cond source =
          .ok (afterCond, false) ∧
        outcome = Outcome.regular afterCond ∧
        finalCtx = ctx) ∨
      (∃ afterCond bodyOutcome,
        Expr.evalCondition model prim cond source =
          .ok (afterCond, true) ∧
        Control.Block.runScoped model prim program ctx body fuel afterCond =
          .ok bodyOutcome ∧
        outcome = bodyOutcome ∧
        finalCtx = ctx) := by
  unfold Control.Stmt.run at hRun
  cases hCond : Expr.evalCondition model prim cond source with
  | error err =>
      simp [hCond] at hRun
  | ok result =>
      rcases result with ⟨afterCond, condTrue⟩
      cases condTrue with
      | false =>
          simp only [hCond, Bool.false_eq_true, ↓reduceIte] at hRun
          left
          refine ⟨afterCond, rfl, ?_⟩
          have hEq := (Except.ok.inj hRun).symm
          exact
            ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
      | true =>
          simp only [hCond, ↓reduceIte] at hRun
          cases hBody :
              Control.Block.runScoped model prim program ctx body fuel afterCond with
          | error err =>
              simp [hBody] at hRun
          | ok bodyOutcome =>
              simp only [hBody, Bind.bind, Except.bind] at hRun
              right
              refine ⟨afterCond, bodyOutcome, rfl, hBody, ?_⟩
              have hEq := (Except.ok.inj hRun).symm
              exact
                ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩

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
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) source =
      .ok (Outcome.regular afterScrutinee, ctx) := by
  simp [Control.Stmt.run, hScrutinee, hSelect]

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
      Control.Block.runScoped model prim program ctx selected fuel
          afterScrutinee =
        .ok outcome) :
    Control.Stmt.run model prim program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) source =
      .ok (outcome, ctx) := by
  simp [Control.Stmt.run, hScrutinee, hSelect, hBody]

/--
Invert a successful canonical source `switch` at the exact selected-body fuel.
-/
theorem run_switch_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok (outcome, finalCtx)) :
    (∃ afterScrutinee value,
        Expr.evalOne model prim scrutinee source =
          .ok (afterScrutinee, value) ∧
        Source.Switch.select value cases defaultBody = none ∧
        outcome = Outcome.regular afterScrutinee ∧
        finalCtx = ctx) ∨
      (∃ afterScrutinee value selected bodyOutcome,
        Expr.evalOne model prim scrutinee source =
          .ok (afterScrutinee, value) ∧
        Source.Switch.select value cases defaultBody = some selected ∧
        Control.Block.runScoped model prim program ctx selected fuel
            afterScrutinee =
          .ok bodyOutcome ∧
        outcome = bodyOutcome ∧
        finalCtx = ctx) := by
  unfold Control.Stmt.run at hRun
  cases hScrutinee : Expr.evalOne model prim scrutinee source with
  | error err =>
      simp [hScrutinee] at hRun
  | ok result =>
      rcases result with ⟨afterScrutinee, value⟩
      simp only [hScrutinee, Bind.bind, Except.bind] at hRun
      cases hSelect : Source.Switch.select value cases defaultBody with
      | none =>
          simp only [hSelect] at hRun
          left
          refine ⟨afterScrutinee, value, rfl, hSelect, ?_⟩
          have hEq := (Except.ok.inj hRun).symm
          exact
            ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
      | some selected =>
          simp only [hSelect] at hRun
          cases hBody :
              Control.Block.runScoped model prim program ctx selected fuel
                afterScrutinee with
          | error err =>
              simp [hBody] at hRun
          | ok bodyOutcome =>
              simp only [hBody, Bind.bind, Except.bind] at hRun
              right
              refine
                ⟨afterScrutinee, value, selected, bodyOutcome, rfl,
                  hSelect, hBody, ?_⟩
              have hEq := (Except.ok.inj hRun).symm
              exact
                ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩

/--
Invert a successful canonical source `for` at the exact smaller initializer
and loop fuel.

Successful execution has exactly three shapes: a regular initializer followed
by a regular loop, a regular initializer followed by an activation exit, or an
initializer that itself exits the activation.
-/
theorem run_for_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx (fuel + 1)
          (.for_ init cond post body) source =
        .ok (outcome, finalCtx)) :
    (∃ afterInit initCtx loopFinal,
        Control.Block.runOpen model prim program ctx.withoutLoopControl
            fuel init source =
          .ok (Outcome.regular afterInit, initCtx) ∧
        Control.Stmt.runForLoop model prim program initCtx cond
            initCtx.withoutLoopControl post
            (initCtx.withLoopControl initCtx.scope initCtx.scope)
            body fuel afterInit =
          .ok (Outcome.regular loopFinal) ∧
        outcome =
          Outcome.regular (model.restrictTo ctx.scope loopFinal) ∧
        finalCtx = ctx) ∨
      (∃ afterInit initCtx,
        Control.Block.runOpen model prim program ctx.withoutLoopControl
            fuel init source =
          .ok (Outcome.regular afterInit, initCtx) ∧
        Control.Stmt.runForLoop model prim program initCtx cond
            initCtx.withoutLoopControl post
            (initCtx.withLoopControl initCtx.scope initCtx.scope)
            body fuel afterInit =
          .ok outcome ∧
        outcome.IsExit ∧
        finalCtx = ctx) ∨
      (∃ initCtx,
        Control.Block.runOpen model prim program ctx.withoutLoopControl
            fuel init source =
          .ok (outcome, initCtx) ∧
        outcome.IsExit ∧
        finalCtx = ctx) := by
  unfold Control.Stmt.run at hRun
  cases hInit :
      Control.Block.runOpen model prim program ctx.withoutLoopControl
        fuel init source with
  | error err =>
      simp [hInit] at hRun
  | ok initResult =>
      rcases initResult with ⟨⟨afterInit, initMode⟩, initCtx⟩
      simp only [hInit, Bind.bind, Except.bind] at hRun
      cases initMode with
      | regular =>
          cases hLoop :
              Control.Stmt.runForLoop model prim program initCtx cond
                initCtx.withoutLoopControl post
                (initCtx.withLoopControl initCtx.scope initCtx.scope)
                body fuel afterInit with
          | error err =>
              simp [hLoop] at hRun
          | ok loopOutcome =>
              rcases loopOutcome with ⟨loopFinal, loopMode⟩
              simp only [hLoop, Bind.bind, Except.bind] at hRun
              cases loopMode with
              | regular =>
                  left
                  refine
                    ⟨afterInit, initCtx, loopFinal, ?_, ?_, ?_⟩
                  · simpa [Outcome.regular,
                      Locals.Source.Effectful.Outcome.regular] using hInit
                  · simpa [Outcome.regular,
                      Locals.Source.Effectful.Outcome.regular] using hLoop
                  · have hEq := (Except.ok.inj hRun).symm
                    exact
                      ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
              | brk =>
                  simp [Source.invalid, Structured.invalid] at hRun
              | cont =>
                  simp [Source.invalid, Structured.invalid] at hRun
              | leave =>
                  right
                  left
                  refine ⟨afterInit, initCtx, ?_, ?_, ?_, ?_⟩
                  · simpa [Outcome.regular,
                      Locals.Source.Effectful.Outcome.regular] using hInit
                  · have hEq := (Except.ok.inj hRun).symm
                    have hOutcomeEq : outcome = Outcome.leave loopFinal := by
                      simpa [Outcome.leave,
                        Locals.Source.Effectful.Outcome.leave] using
                        congrArg Prod.fst hEq
                    rw [hOutcomeEq]
                    simpa [Outcome.leave,
                      Locals.Source.Effectful.Outcome.leave] using hLoop
                  · have hEq := (Except.ok.inj hRun).symm
                    have hOutcomeEq : outcome = Outcome.leave loopFinal := by
                      simpa [Outcome.leave,
                        Locals.Source.Effectful.Outcome.leave] using
                        congrArg Prod.fst hEq
                    rw [hOutcomeEq]
                    simp [Outcome.IsExit, Outcome.leave,
                      Locals.Source.Effectful.Outcome.leave]
                  · exact congrArg Prod.snd (Except.ok.inj hRun).symm
              | halt kind =>
                  right
                  left
                  refine ⟨afterInit, initCtx, ?_, ?_, ?_, ?_⟩
                  · simpa [Outcome.regular,
                      Locals.Source.Effectful.Outcome.regular] using hInit
                  · have hEq := (Except.ok.inj hRun).symm
                    have hOutcomeEq : outcome = Outcome.halt kind loopFinal := by
                      simpa [Outcome.halt,
                        Locals.Source.Effectful.Outcome.halt] using
                        congrArg Prod.fst hEq
                    rw [hOutcomeEq]
                    simpa [Outcome.halt,
                      Locals.Source.Effectful.Outcome.halt] using hLoop
                  · have hEq := (Except.ok.inj hRun).symm
                    have hOutcomeEq : outcome = Outcome.halt kind loopFinal := by
                      simpa [Outcome.halt,
                        Locals.Source.Effectful.Outcome.halt] using
                        congrArg Prod.fst hEq
                    rw [hOutcomeEq]
                    simp [Outcome.IsExit, Outcome.halt,
                      Locals.Source.Effectful.Outcome.halt]
                  · exact congrArg Prod.snd (Except.ok.inj hRun).symm
      | brk =>
          simp [Source.invalid, Structured.invalid] at hRun
      | cont =>
          simp [Source.invalid, Structured.invalid] at hRun
      | leave =>
          right
          right
          refine ⟨initCtx, ?_, ?_, ?_⟩
          · have hEq := (Except.ok.inj hRun).symm
            have hOutcomeEq : outcome = Outcome.leave afterInit := by
              simpa [Outcome.leave,
                Locals.Source.Effectful.Outcome.leave] using
                congrArg Prod.fst hEq
            rw [hOutcomeEq]
            simpa [Outcome.leave,
              Locals.Source.Effectful.Outcome.leave] using hInit
          · have hEq := (Except.ok.inj hRun).symm
            have hOutcomeEq : outcome = Outcome.leave afterInit := by
              simpa [Outcome.leave,
                Locals.Source.Effectful.Outcome.leave] using
                congrArg Prod.fst hEq
            rw [hOutcomeEq]
            simp [Outcome.IsExit, Outcome.leave,
              Locals.Source.Effectful.Outcome.leave]
          · exact congrArg Prod.snd (Except.ok.inj hRun).symm
      | halt kind =>
          right
          right
          refine ⟨initCtx, ?_, ?_, ?_⟩
          · have hEq := (Except.ok.inj hRun).symm
            have hOutcomeEq : outcome = Outcome.halt kind afterInit := by
              simpa [Outcome.halt,
                Locals.Source.Effectful.Outcome.halt] using
                congrArg Prod.fst hEq
            rw [hOutcomeEq]
            simpa [Outcome.halt,
              Locals.Source.Effectful.Outcome.halt] using hInit
          · have hEq := (Except.ok.inj hRun).symm
            have hOutcomeEq : outcome = Outcome.halt kind afterInit := by
              simpa [Outcome.halt,
                Locals.Source.Effectful.Outcome.halt] using
                congrArg Prod.fst hEq
            rw [hOutcomeEq]
            simp [Outcome.IsExit, Outcome.halt,
              Locals.Source.Effectful.Outcome.halt]
          · exact congrArg Prod.snd (Except.ok.inj hRun).symm

end Stmt

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpen_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Source.Ctx} {block : Block}
        {state : σ} {outcome : Outcome σ} {runCtx : Source.Ctx},
        fuel ≤ fuel' →
        Control.Block.runOpen model prim program ctx fuel block state =
          .ok (outcome, runCtx) →
        Control.Block.runOpen model prim program ctx fuel' block state =
          .ok (outcome, runCtx) := by
    intro fuel fuel' ctx block state outcome runCtx hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hRun
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
                    simpa [Control.Block.runOpen] using hRun
                | cons stmt rest =>
                    cases hStmt :
                        Control.Stmt.run model prim program ctx fuel stmt state with
                    | error err =>
                        simp [Control.Block.runOpen, hStmt] at hRun
                    | ok stmtResult =>
                        rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                        have hStmt' :
                            Control.Stmt.run model prim program ctx fuel' stmt state =
                              .ok (stmtOutcome, stmtCtx) :=
                          Stmt.run_mono model prim program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Control.Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact
                              Block.runOpen_mono model prim program
                                hFuelLe hRun
                        | brk =>
                            simp [Control.Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Control.Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Control.Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Control.Block.runOpen, hStmt, hStmt', hMode]
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
        Control.Block.runScoped model prim program ctx block fuel state =
          .ok outcome →
        Control.Block.runScoped model prim program ctx block fuel' state =
          .ok outcome := by
    intro fuel fuel' ctx block state outcome hLe hRun
    unfold Control.Block.runScoped at hRun ⊢
    cases hOpen :
        Control.Block.runOpen model prim program ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        have hOpen' :
            Control.Block.runOpen model prim program ctx fuel' block state =
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
        Control.FunDef.runBody model prim program fn args fuel state = .ok result →
        Control.FunDef.runBody model prim program fn args fuel' state = .ok result := by
    intro fuel fuel' fn args state result hLe hRun
    cases fuel with
    | zero =>
        simp [Control.FunDef.runBody, Source.invalid, Structured.invalid] at hRun
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
                simp [Control.FunDef.runBody, hParams, Source.invalid,
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
                    Control.Block.runOpen model prim program bodyCtx fuel fn.body
                      initialState with
                | error err =>
                    simp [Control.FunDef.runBody, hParams, initialStore,
                      callerSource, initialSource, initialState,
                      functionScope, bodyCtx, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with ⟨bodyOutcome, bodyFinalCtx⟩
                    have hBody' :
                        Control.Block.runOpen model prim program bodyCtx fuel' fn.body
                            initialState =
                          .ok (bodyOutcome, bodyFinalCtx) :=
                      Block.runOpen_mono model prim program hFuelLe hBody
                    cases hMode : bodyOutcome.mode with
                    | regular =>
                        simp [Control.FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
                    | brk =>
                        simp [Control.FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode,
                          Source.invalid, Structured.invalid] at hRun
                    | cont =>
                        simp [Control.FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode,
                          Source.invalid, Structured.invalid] at hRun
                    | leave =>
                        simp [Control.FunDef.runBody, hParams, initialStore,
                          callerSource, initialSource, initialState,
                          functionScope, bodyCtx, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [Control.FunDef.runBody, hParams, initialStore,
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
        Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel state = .ok outcome →
        Control.Stmt.runForLoop model prim program loopCtx cond postBase post
          bodyBase body fuel' state = .ok outcome := by
    intro fuel fuel' loopCtx cond postBase post bodyBase body state outcome
      hLe hRun
    cases fuel with
    | zero =>
        simp [Control.Stmt.runForLoop, Source.invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Control.Stmt.runForLoop at hRun ⊢
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
                        Control.Block.runScoped model prim program bodyBase body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Control.Block.runScoped model prim program bodyBase body
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
                                Control.Block.runScoped model prim program postBase
                                  post fuel bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Control.Block.runScoped model prim program
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
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | cont =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Control.Block.runScoped model prim program postBase
                                  post fuel bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Control.Block.runScoped model prim program
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
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
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
        Control.Stmt.run model prim program ctx fuel stmt state =
          .ok (outcome, runCtx) →
        Control.Stmt.run model prim program ctx fuel' stmt state =
          .ok (outcome, runCtx) := by
    intro fuel fuel' ctx stmt state outcome runCtx hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Control.Stmt.run] using hRun
    | let_ name value =>
        simpa [Control.Stmt.run] using hRun
    | assign name value =>
        simpa [Control.Stmt.run] using hRun
    | block body =>
        unfold Control.Stmt.run at hRun ⊢
        cases hBody :
            Control.Block.runScoped model prim program ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            have hBody' :
                Control.Block.runScoped model prim program ctx body fuel' state =
                  .ok bodyOutcome :=
              Block.runScoped_mono model prim program hLe hBody
            simp [hBody, hBody'] at hRun ⊢
            exact hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Control.Stmt.run at hRun ⊢
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
                            Control.Block.runScoped model prim program ctx body fuel
                              stateAfterCond with
                        | error err =>
                            simp [hBody] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Control.Block.runScoped model prim program ctx body
                                    fuel' stateAfterCond =
                                  .ok bodyOutcome :=
                              Block.runScoped_mono model prim program
                                hFuelLe hBody
                            simp [hBody, hBody'] at hRun ⊢
                            exact hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Control.Stmt.run at hRun ⊢
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
                            Control.Block.runScoped model prim program ctx selected
                              fuel stateAfterScrutinee with
                        | error err =>
                            simpa [hBody] using hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Control.Block.runScoped model prim program ctx selected
                                    fuel' stateAfterScrutinee =
                                  .ok bodyOutcome :=
                              Block.runScoped_mono model prim program
                                hFuelLe hBody
                            simpa [hBody, hBody'] using hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Control.Stmt.run at hRun ⊢
                let initBase := ctx.withoutLoopControl
                cases hInit :
                    Control.Block.runOpen model prim program initBase fuel init state
                with
                | error err =>
                    simp [initBase, hInit] at hRun
                | ok initResult =>
                    rcases initResult with ⟨initOutcome, initCtx⟩
                    have hInit' :
                        Control.Block.runOpen model prim program initBase fuel' init
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
                            Control.Stmt.runForLoop model prim program loopCtx cond
                              postBase post bodyBase body fuel
                              initOutcome.state with
                        | error err =>
                            simp [loopCtx, postBase, bodyBase, hLoop] at hRun
                        | ok loopOutcome =>
                            have hLoop' :
                                Control.Stmt.runForLoop model prim program loopCtx cond
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
        simpa [Control.Stmt.run] using hRun
    | cont =>
        simpa [Control.Stmt.run] using hRun
    | leave =>
        simpa [Control.Stmt.run] using hRun
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Control.Stmt.run, Source.invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Control.Stmt.run at hRun ⊢
                by_cases hTargets : targets.Nodup
                · simp [hTargets] at hRun ⊢
                  cases hArgs :
                      ArgList.Control.eval model prim args state with
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
                              Control.FunDef.runBody model prim program fn argValues
                                fuel stateAfterArgs with
                          | error err =>
                              simp [hArgs, hLookup, hBody] at hRun
                          | ok callResult =>
                              have hBody' :
                                  Control.FunDef.runBody model prim program fn
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
        simpa [Control.Stmt.run] using hRun
    | terminalArgs kind args =>
        simpa [Control.Stmt.run] using hRun
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

/--
Successful statement execution has a unique outcome and context, independently
of which sufficient fuel bound was used.
-/
theorem Stmt.run_success_unique {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {leftFuel rightFuel : Nat}
    {ctx leftCtx rightCtx : Source.Ctx}
    {stmt : Stmt} {source : σ}
    {leftOutcome rightOutcome : Outcome σ}
    (hLeft :
      Control.Stmt.run model prim program ctx leftFuel stmt source =
        .ok (leftOutcome, leftCtx))
    (hRight :
      Control.Stmt.run model prim program ctx rightFuel stmt source =
        .ok (rightOutcome, rightCtx)) :
    (leftOutcome, leftCtx) = (rightOutcome, rightCtx) := by
  let commonFuel := Nat.max leftFuel rightFuel
  have hLeft' :
      Control.Stmt.run model prim program ctx commonFuel stmt source =
        .ok (leftOutcome, leftCtx) :=
    Stmt.run_mono model prim program (Nat.le_max_left _ _) hLeft
  have hRight' :
      Control.Stmt.run model prim program ctx commonFuel stmt source =
        .ok (rightOutcome, rightCtx) :=
    Stmt.run_mono model prim program (Nat.le_max_right _ _) hRight
  rw [hLeft'] at hRight'
  exact Except.ok.inj hRight'

namespace Block

/--
An empty open block succeeds at every positive fuel with the unchanged regular
state and context.
-/
theorem runOpen_nil {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program) (ctx : Source.Ctx) (fuel : Nat) (state : σ) :
    Control.Block.runOpen model prim program ctx (fuel + 1)
        { stmts := [] } state =
      .ok (Outcome.regular state, ctx) := by
  simp [Control.Block.runOpen, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
Successful empty open-block execution is the unchanged regular state and
context.
-/
theorem runOpen_nil_ok {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx : Source.Ctx} {fuel : Nat} {state : σ}
    {outcome : Outcome σ} {runCtx : Source.Ctx}
    (hRun :
      Control.Block.runOpen model prim program ctx fuel { stmts := [] } state =
        .ok (outcome, runCtx)) :
    outcome = Outcome.regular state ∧ runCtx = ctx := by
  cases fuel with
  | zero =>
      simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      have hPair :
          (Outcome.regular state, ctx) = (outcome, runCtx) := by
        simpa [Control.Block.runOpen] using hRun
      injection hPair with hOutcome hCtx
      exact ⟨hOutcome.symm, hCtx.symm⟩

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
      Control.Block.runOpen model prim program ctx fuel block source =
        .ok (Outcome.regular final, finalCtx)) :
    Control.Block.runScoped model prim program ctx block fuel source =
      .ok (Outcome.regular (model.restrictTo ctx.scope final)) := by
  simp [Control.Block.runScoped, hOpen, Outcome.regular,
    Locals.Source.Effectful.Outcome.regular]

/--
A regular open-block result may be exposed through any extensionally equal
scope list. Source lexical scope is set-like even when compiler live lists use
a representation-specific order.
-/
theorem runScoped_regular_of_runOpen_scope {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {block : Block} {source final : σ}
    {scope : List Name}
    (hOpen :
      Control.Block.runOpen model prim program ctx fuel block source =
        .ok (Outcome.regular final, finalCtx))
    (hScope : ∀ name, name ∈ ctx.scope ↔ name ∈ scope) :
    Control.Block.runScoped model prim program ctx block fuel source =
      .ok (Outcome.regular (model.restrictTo scope final)) := by
  have hScoped :=
    runScoped_regular_of_runOpen model prim program hOpen
  rw [Locals.Source.Effectful.StateModel.restrictTo_congr
    model hScope] at hScoped
  exact hScoped

/--
Abrupt open-block outcomes pass through scoped execution unchanged.
-/
theorem runScoped_nonregular_of_runOpen {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {block : Block} {source : σ} {outcome : Outcome σ}
    (hOpen :
      Control.Block.runOpen model prim program ctx fuel block source =
        .ok (outcome, finalCtx))
    (hMode : outcome.mode ≠ .regular) :
    Control.Block.runScoped model prim program ctx block fuel source =
      .ok outcome := by
  cases hOutcome : outcome.mode with
  | regular =>
      exact False.elim (hMode hOutcome)
  | brk =>
      simp [Control.Block.runScoped, hOpen, hOutcome]
  | cont =>
      simp [Control.Block.runScoped, hOpen, hOutcome]
  | leave =>
      simp [Control.Block.runScoped, hOpen, hOutcome]
  | halt kind =>
      simp [Control.Block.runScoped, hOpen, hOutcome]

/--
Invert successful lexical execution into its exact open-block run.

Regular execution exposes the source restriction performed at scope exit;
abrupt execution exposes the unchanged open outcome. This keeps recursive
compiler proofs on the canonical Functions interpreter.
-/
theorem runScoped_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx : Source.Ctx} {fuel : Nat}
    {block : Block} {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Block.runScoped model prim program ctx block fuel source =
        .ok outcome) :
    (∃ final finalCtx,
        Control.Block.runOpen model prim program ctx fuel block source =
          .ok (Outcome.regular final, finalCtx) ∧
        outcome =
          Outcome.regular (model.restrictTo ctx.scope final)) ∨
      (∃ openOutcome finalCtx,
        Control.Block.runOpen model prim program ctx fuel block source =
          .ok (openOutcome, finalCtx) ∧
        openOutcome.mode ≠ .regular ∧
        outcome = openOutcome) := by
  unfold Control.Block.runScoped at hRun
  cases hOpen :
      Control.Block.runOpen model prim program ctx fuel block source with
  | error err =>
      simp [hOpen] at hRun
  | ok openResult =>
      rcases openResult with ⟨openOutcome, finalCtx⟩
      cases hMode : openOutcome.mode with
      | regular =>
          simp only [hOpen, Bind.bind, Except.bind, hMode] at hRun
          rcases openOutcome with ⟨final, mode⟩
          cases hMode
          left
          refine ⟨final, finalCtx, rfl, ?_⟩
          exact (Except.ok.inj hRun).symm
      | brk =>
          simp only [hOpen, Bind.bind, Except.bind, hMode] at hRun
          right
          refine ⟨openOutcome, finalCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · exact (Except.ok.inj hRun).symm
      | cont =>
          simp only [hOpen, Bind.bind, Except.bind, hMode] at hRun
          right
          refine ⟨openOutcome, finalCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · exact (Except.ok.inj hRun).symm
      | leave =>
          simp only [hOpen, Bind.bind, Except.bind, hMode] at hRun
          right
          refine ⟨openOutcome, finalCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · exact (Except.ok.inj hRun).symm
      | halt kind =>
          simp only [hOpen, Bind.bind, Except.bind, hMode] at hRun
          right
          refine ⟨openOutcome, finalCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · exact (Except.ok.inj hRun).symm

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
      Control.Stmt.run model prim program ctx headFuel stmt source =
        .ok (Outcome.regular mid, midCtx))
    (hTail :
      Control.Block.runOpen model prim program midCtx tailFuel
          { stmts := rest } mid =
        .ok (outcome, finalCtx)) :
    ∃ fuel,
      Control.Block.runOpen model prim program ctx fuel
          { stmts := stmt :: rest } source =
        .ok (outcome, finalCtx) := by
  let commonFuel := Nat.max headFuel tailFuel
  have hHead' :
      Control.Stmt.run model prim program ctx commonFuel stmt source =
        .ok (Outcome.regular mid, midCtx) :=
    Stmt.run_mono model prim program (Nat.le_max_left _ _) hHead
  have hTail' :
      Control.Block.runOpen model prim program midCtx commonFuel
          { stmts := rest } mid =
        .ok (outcome, finalCtx) :=
    Block.runOpen_mono model prim program (Nat.le_max_right _ _) hTail
  exact
    ⟨commonFuel + 1,
      by simp [Control.Block.runOpen, hHead', hTail',
        Outcome.regular, Locals.Source.Effectful.Outcome.regular]⟩

/--
Compose a regular head statement and tail at their exact canonical
`max + 1` open-block budget.
-/
theorem runOpen_cons_regular_at_max {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {headFuel tailFuel : Nat} {ctx midCtx finalCtx : Source.Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {source mid : σ} {outcome : Outcome σ}
    (hHead :
      Control.Stmt.run model prim program ctx headFuel stmt source =
        .ok (Outcome.regular mid, midCtx))
    (hTail :
      Control.Block.runOpen model prim program midCtx tailFuel
          { stmts := rest } mid =
        .ok (outcome, finalCtx)) :
    Control.Block.runOpen model prim program ctx
        (Nat.max headFuel tailFuel + 1)
        { stmts := stmt :: rest } source =
      .ok (outcome, finalCtx) := by
  let commonFuel := Nat.max headFuel tailFuel
  have hHead' :
      Control.Stmt.run model prim program ctx commonFuel stmt source =
        .ok (Outcome.regular mid, midCtx) :=
    Stmt.run_mono model prim program (Nat.le_max_left _ _) hHead
  have hTail' :
      Control.Block.runOpen model prim program midCtx commonFuel
          { stmts := rest } mid =
        .ok (outcome, finalCtx) :=
    Block.runOpen_mono model prim program (Nat.le_max_right _ _) hTail
  dsimp [commonFuel] at hHead' hTail'
  simp [Control.Block.runOpen, hHead', hTail',
    Outcome.regular, Locals.Source.Effectful.Outcome.regular]

/--
Invert one successful nonempty open-block execution at its canonical
one-smaller statement fuel.

The head either finishes regularly and exposes the exact recursive tail run,
or exits abruptly and fixes the whole block outcome while making the tail
unreachable. This is the semantic-owner interface used by recursive compiler
proofs; callers do not need to unfold the block interpreter themselves.
-/
theorem runOpen_cons_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {fuel : Nat} {ctx finalCtx : Source.Ctx}
    {stmt : Stmt} {rest : List Stmt}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Block.runOpen model prim program ctx (fuel + 1)
          { stmts := stmt :: rest } source =
        .ok (outcome, finalCtx)) :
    (∃ mid midCtx,
        Control.Stmt.run model prim program ctx fuel stmt source =
          .ok (Outcome.regular mid, midCtx) ∧
        Control.Block.runOpen model prim program midCtx fuel
            { stmts := rest } mid =
          .ok (outcome, finalCtx)) ∨
      (∃ headOutcome headCtx,
        Control.Stmt.run model prim program ctx fuel stmt source =
          .ok (headOutcome, headCtx) ∧
        headOutcome.mode ≠ .regular ∧
        outcome = headOutcome ∧
        finalCtx = ctx) := by
  cases hHead :
      Control.Stmt.run model prim program ctx fuel stmt source with
  | error err =>
      simp [Control.Block.runOpen, hHead] at hRun
  | ok headResult =>
      rcases headResult with ⟨headOutcome, headCtx⟩
      cases hMode : headOutcome.mode with
      | regular =>
          rcases headOutcome with ⟨headState, headMode⟩
          cases hMode
          left
          refine ⟨headState, headCtx, rfl, ?_⟩
          · simpa [Control.Block.runOpen, hHead] using hRun
      | brk =>
          right
          refine ⟨headOutcome, headCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · simpa [Control.Block.runOpen, hHead, hMode] using hRun.symm
      | cont =>
          right
          refine ⟨headOutcome, headCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · simpa [Control.Block.runOpen, hHead, hMode] using hRun.symm
      | leave =>
          right
          refine ⟨headOutcome, headCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · simpa [Control.Block.runOpen, hHead, hMode] using hRun.symm
      | halt kind =>
          right
          refine ⟨headOutcome, headCtx, rfl, ?_, ?_⟩
          · simp [hMode]
          · simpa [Control.Block.runOpen, hHead, hMode] using hRun.symm

/--
Expose the scoped body execution represented by a successful singleton
`block` statement. This is the semantic-owner bridge used by adjacent source
passes whose own control construct lowers to a Functions scoped body.
-/
theorem runScoped_of_runOpen_singleton_block {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx : Source.Ctx} {body : Block} {source : σ}
    {outcome : Outcome σ} {finalCtx : Source.Ctx}
    (hRun :
      ∃ fuel,
        Control.Block.runOpen model prim program ctx fuel
            { stmts := [.block body] } source =
          .ok (outcome, finalCtx)) :
    ∃ fuel,
      Control.Block.runScoped model prim program ctx body fuel source =
        .ok outcome ∧
      finalCtx = ctx := by
  obtain ⟨fuel, hRun⟩ := hRun
  cases fuel with
  | zero =>
      simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hRun
  | succ fuel =>
      rcases runOpen_cons_cases model prim program hRun with
        hRegular | hNonregular
      · obtain ⟨middle, middleCtx, hStmt, hTail⟩ := hRegular
        have hStmtParts :
            Control.Block.runScoped model prim program ctx body fuel source =
                .ok (Outcome.regular middle) ∧
              middleCtx = ctx := by
          unfold Control.Stmt.run at hStmt
          cases hBody :
              Control.Block.runScoped model prim program ctx body fuel source with
          | error err =>
              simp [hBody] at hStmt
          | ok bodyOutcome =>
              have hPair :
                  (bodyOutcome, ctx) =
                    (Outcome.regular middle, middleCtx) := by
                simpa [hBody] using hStmt
              injection hPair with hOutcome hStmtCtx
              exact
                ⟨by simpa [hOutcome] using hBody, hStmtCtx.symm⟩
        obtain ⟨hOutcome, hTailCtx⟩ :=
          runOpen_nil_ok model prim program hTail
        rw [hOutcome]
        exact
          ⟨fuel, hStmtParts.1,
            hTailCtx.trans hStmtParts.2⟩
      · obtain
          ⟨headOutcome, headCtx, hStmt, _hMode,
            hOutcome, hCtx⟩ := hNonregular
        have hScoped :
            Control.Block.runScoped model prim program ctx body fuel source =
              .ok headOutcome := by
          unfold Control.Stmt.run at hStmt
          cases hBody :
              Control.Block.runScoped model prim program ctx body fuel source with
          | error err =>
              simp [hBody] at hStmt
          | ok bodyOutcome =>
              have hPair :
                  (bodyOutcome, ctx) = (headOutcome, headCtx) := by
                simpa [hBody] using hStmt
              injection hPair with hOutcome _hCtx
              simpa [hOutcome] using hBody
        rw [hOutcome]
        exact ⟨fuel, hScoped, hCtx⟩

/--
Expose a singleton `block` body at the same fuel as the enclosing successful
open-block execution. The body itself runs one level lower; fuel monotonicity
raises that checked execution to the caller's index.
-/
theorem runScoped_at_of_runOpen_singleton_block {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {fuel : Nat} {ctx : Source.Ctx} {body : Block} {source : σ}
    {outcome : Outcome σ} {finalCtx : Source.Ctx}
    (hRun :
      Control.Block.runOpen model prim program ctx fuel
          { stmts := [.block body] } source =
        .ok (outcome, finalCtx)) :
    Control.Block.runScoped model prim program ctx body fuel source =
        .ok outcome ∧
      finalCtx = ctx := by
  cases fuel with
  | zero =>
      simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hRun
  | succ previous =>
      rcases runOpen_cons_cases model prim program hRun with
        hRegular | hNonregular
      · obtain ⟨middle, middleCtx, hStmt, hTail⟩ := hRegular
        have hStmtParts :
            Control.Block.runScoped model prim program ctx body previous source =
                .ok (Outcome.regular middle) ∧
              middleCtx = ctx := by
          unfold Control.Stmt.run at hStmt
          cases hBody :
              Control.Block.runScoped model prim program ctx body previous source with
          | error err =>
              simp [hBody] at hStmt
          | ok bodyOutcome =>
              have hPair :
                  (bodyOutcome, ctx) =
                    (Outcome.regular middle, middleCtx) := by
                simpa [hBody] using hStmt
              injection hPair with hOutcome hStmtCtx
              exact
                ⟨by simpa [hOutcome] using hBody, hStmtCtx.symm⟩
        obtain ⟨hOutcome, hTailCtx⟩ :=
          runOpen_nil_ok model prim program hTail
        rw [hOutcome]
        exact
          ⟨Block.runScoped_mono model prim program
              (Nat.le_succ previous) hStmtParts.1,
            hTailCtx.trans hStmtParts.2⟩
      · obtain
          ⟨headOutcome, headCtx, hStmt, _hMode,
            hOutcome, hCtx⟩ := hNonregular
        have hScoped :
            Control.Block.runScoped model prim program ctx body previous source =
              .ok headOutcome := by
          unfold Control.Stmt.run at hStmt
          cases hBody :
              Control.Block.runScoped model prim program ctx body previous source with
          | error err =>
              simp [hBody] at hStmt
          | ok bodyOutcome =>
              have hPair :
                  (bodyOutcome, ctx) = (headOutcome, headCtx) := by
                simpa [hBody] using hStmt
              injection hPair with hOutcome _hCtx
              simpa [hOutcome] using hBody
        rw [hOutcome]
        exact
          ⟨Block.runScoped_mono model prim program
              (Nat.le_succ previous) hScoped,
            hCtx⟩

/--
Successful open-block execution never removes names from its lexical context.
Regular heads may extend the context through declarations; abrupt heads return
the block's incoming context.
-/
theorem runOpen_scopeExtends {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program) :
    ∀ {fuel : Nat} {ctx finalCtx : Source.Ctx}
      {block : Block} {source : σ} {outcome : Outcome σ},
      Control.Block.runOpen model prim program ctx fuel block source =
          .ok (outcome, finalCtx) →
        Source.Ctx.ScopeExtends ctx finalCtx := by
  intro fuel
  induction fuel with
  | zero =>
      intro ctx finalCtx block source outcome hRun
      simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hRun
  | succ fuel ih =>
      intro ctx finalCtx block source outcome hRun
      rcases block with ⟨stmts⟩
      cases stmts with
      | nil =>
          obtain ⟨_hOutcome, hCtx⟩ :=
            runOpen_nil_ok model prim program hRun
          subst finalCtx
          exact Source.Ctx.ScopeExtends.refl ctx
      | cons stmt rest =>
          rcases
              runOpen_cons_cases model prim program hRun with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨middle, middleCtx, hStmt, hRest⟩
            exact
              Source.Ctx.ScopeExtends.trans
                (Stmt.run_scopeExtends model prim program hStmt)
                (ih hRest)
          · rcases hNonregular with
              ⟨headOutcome, headCtx, _hHead, _hMode,
                _hOutcome, hCtx⟩
            subst finalCtx
            exact Source.Ctx.ScopeExtends.refl ctx

/--
Compose two successful effectful open-block fragments when the first fragment
returns regularly.
-/
theorem runOpen_append_regular_exists {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program) :
    ∀ (left right : List Stmt) (ctx midCtx : Source.Ctx)
      (source mid : σ) (outcome : Outcome σ) (runCtx : Source.Ctx),
      (∃ fuel,
        Control.Block.runOpen model prim program ctx fuel { stmts := left } source =
          .ok (Outcome.regular mid, midCtx)) →
      (∃ fuel,
        Control.Block.runOpen model prim program midCtx fuel { stmts := right } mid =
          .ok (outcome, runCtx)) →
      ∃ fuel,
        Control.Block.runOpen model prim program ctx fuel
            { stmts := left ++ right } source =
          .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx midCtx source mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuel, hLeft⟩
      rcases runOpen_nil_ok model prim program hLeft with
        ⟨hOutcome, hCtx⟩
      cases hOutcome
      cases hCtx
      simpa using hRight
  | cons stmt rest ih =>
      intro right ctx midCtx source mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuel, hLeft⟩
      cases fuel with
      | zero =>
          simp [Control.Block.runOpen, Source.invalid, Structured.invalid] at hLeft
      | succ fuel =>
          rcases
              runOpen_cons_cases model prim program
                (fuel := fuel) hLeft with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨afterStmt, stmtCtx, hStmt, hRest⟩
            obtain ⟨tailFuel, hTail⟩ :=
              ih right stmtCtx midCtx afterStmt mid outcome runCtx
                ⟨fuel, hRest⟩ hRight
            exact
              runOpen_cons_regular_exists model prim program
                hStmt hTail
          · rcases hNonregular with
              ⟨headOutcome, headCtx, _hHead, hMode, hOutcome, _hCtx⟩
            rw [← hOutcome] at hMode
            simp [Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hMode

/--
Compose two regular open-block executions at an explicit additive fuel budget.
Upper compiler passes use this theorem to retain quantitative bounds without
unfolding the canonical Functions interpreter.
-/
theorem runOpen_append_regular_at_add {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program) :
    ∀ (left right : List Stmt) (ctx midCtx : Source.Ctx)
      (source mid : σ) (outcome : Outcome σ) (runCtx : Source.Ctx)
      (leftFuel rightFuel : Nat),
      Control.Block.runOpen model prim program ctx leftFuel
          { stmts := left } source =
        .ok (Outcome.regular mid, midCtx) →
      Control.Block.runOpen model prim program midCtx rightFuel
          { stmts := right } mid =
        .ok (outcome, runCtx) →
      Control.Block.runOpen model prim program ctx (leftFuel + rightFuel)
          { stmts := left ++ right } source =
        .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx midCtx source mid outcome runCtx
        leftFuel rightFuel hLeft hRight
      rcases runOpen_nil_ok model prim program hLeft with
        ⟨hOutcome, hCtx⟩
      cases hOutcome
      cases hCtx
      simpa using
        Block.runOpen_mono model prim program
          (by omega : rightFuel ≤ leftFuel + rightFuel) hRight
  | cons stmt rest ih =>
      intro right ctx midCtx source mid outcome runCtx
        leftFuel rightFuel hLeft hRight
      cases leftFuel with
      | zero =>
          simp [Control.Block.runOpen, Source.invalid,
            Structured.invalid] at hLeft
      | succ fuel =>
          rcases
              runOpen_cons_cases model prim program
                (fuel := fuel) hLeft with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨afterStmt, stmtCtx, hStmt, hRest⟩
            have hTail :=
              ih right stmtCtx midCtx afterStmt mid outcome runCtx
                fuel rightFuel hRest hRight
            have hHead :
                Control.Stmt.run model prim program ctx (fuel + rightFuel)
                    stmt source =
                  .ok (Outcome.regular afterStmt, stmtCtx) :=
              Stmt.run_mono model prim program
                (by omega : fuel ≤ fuel + rightFuel) hStmt
            simpa [Control.Block.runOpen, hHead, hTail, Nat.succ_add,
              Outcome.regular,
              Locals.Source.Effectful.Outcome.regular]
          · rcases hNonregular with
              ⟨headOutcome, headCtx, _hHead, hMode,
                hOutcome, _hCtx⟩
            rw [← hOutcome] at hMode
            simp [Outcome.regular,
              Locals.Source.Effectful.Outcome.regular] at hMode

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
      Control.Stmt.run model prim program ctx fuel stmt source =
        .ok (outcome, stmtCtx))
    (hMode : outcome.mode ≠ .regular) :
    Control.Block.runOpen model prim program ctx (fuel + 1)
        { stmts := stmt :: rest } source =
      .ok (outcome, ctx) := by
  cases hOutcomeMode : outcome.mode with
  | regular =>
      exact False.elim (hMode hOutcomeMode)
  | brk =>
      simp [Control.Block.runOpen, hHead, hOutcomeMode]
  | cont =>
      simp [Control.Block.runOpen, hHead, hOutcomeMode]
  | leave =>
      simp [Control.Block.runOpen, hHead, hOutcomeMode]
  | halt kind =>
      simp [Control.Block.runOpen, hHead, hOutcomeMode]

/--
Lift one successful statement that restores its incoming context to a
singleton open-block execution. Regular outcomes execute the empty tail;
abrupt outcomes skip it.
-/
theorem runOpen_singleton_of_run {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx : Source.Ctx} {stmtFuel : Nat}
    {stmt : Stmt} {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx stmtFuel stmt source =
        .ok (outcome, ctx)) :
    ∃ fuel,
      Control.Block.runOpen model prim program ctx fuel
          { stmts := [stmt] } source =
        .ok (outcome, ctx) := by
  by_cases hRegular : outcome.mode = .regular
  · have hOutcomeEq :
        outcome = Outcome.regular outcome.state :=
      Outcome.eq_regular_of_mode hRegular
    have hStmt :
        Control.Stmt.run model prim program ctx stmtFuel stmt source =
          .ok (Outcome.regular outcome.state, ctx) := by
      rw [← hOutcomeEq]
      exact hRun
    have hEmpty :
        Control.Block.runOpen model prim program ctx 1
            { stmts := [] } outcome.state =
          .ok (Outcome.regular outcome.state, ctx) := by
      simpa using runOpen_nil model prim program ctx 0 outcome.state
    obtain ⟨fuel, hSingleton⟩ :=
      runOpen_cons_regular_exists model prim program hStmt hEmpty
    rw [← hOutcomeEq] at hSingleton
    exact ⟨fuel, hSingleton⟩
  · exact
      ⟨stmtFuel + 1,
        runOpen_cons_nonregular model prim program hRun hRegular⟩

/--
Lift one successful statement to a singleton open block at a uniform
`stmtFuel + 2` budget. The extra unit covers the empty regular tail; abrupt
outcomes are raised to the same budget by fuel monotonicity.
-/
theorem runOpen_singleton_of_run_at_add_two {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx : Source.Ctx} {stmtFuel : Nat}
    {stmt : Stmt} {source : σ} {outcome : Outcome σ}
    (hRun :
      Control.Stmt.run model prim program ctx stmtFuel stmt source =
        .ok (outcome, ctx)) :
    Control.Block.runOpen model prim program ctx (stmtFuel + 2)
        { stmts := [stmt] } source =
      .ok (outcome, ctx) := by
  by_cases hRegular : outcome.mode = .regular
  · have hOutcomeEq :
        outcome = Outcome.regular outcome.state :=
      Outcome.eq_regular_of_mode hRegular
    have hStmt :
        Control.Stmt.run model prim program ctx (stmtFuel + 1) stmt source =
          .ok (Outcome.regular outcome.state, ctx) := by
      rw [← hOutcomeEq]
      exact
        Stmt.run_mono model prim program
          (by omega : stmtFuel ≤ stmtFuel + 1) hRun
    have hEmpty :
        Control.Block.runOpen model prim program ctx (stmtFuel + 1)
            { stmts := [] } outcome.state =
          .ok (Outcome.regular outcome.state, ctx) := by
      simpa using
        runOpen_nil model prim program ctx stmtFuel outcome.state
    rw [hOutcomeEq]
    simpa [Control.Block.runOpen, hStmt, hEmpty,
      Outcome.regular,
      Locals.Source.Effectful.Outcome.regular]
  · exact
      Block.runOpen_mono model prim program
        (by omega : stmtFuel + 1 ≤ stmtFuel + 2)
        (runOpen_cons_nonregular model prim program hRun hRegular)

/--
Lift a nonregular open body through the canonical scoped `block` statement and
then through a singleton open block. The enclosing lexical scope performs no
restriction on abrupt outcomes.
-/
theorem runOpen_singleton_block_of_runOpen_nonregular {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {ctx finalCtx : Source.Ctx}
    {body : Block} {source : σ} {outcome : Outcome σ}
    (hBody :
      ∃ fuel,
        Control.Block.runOpen model prim program ctx fuel body source =
          .ok (outcome, finalCtx))
    (hMode : outcome.mode ≠ .regular) :
    ∃ fuel,
      Control.Block.runOpen model prim program ctx fuel
          { stmts := [.block body] } source =
        .ok (outcome, ctx) := by
  obtain ⟨bodyFuel, hBody⟩ := hBody
  have hScoped :
      Control.Block.runScoped model prim program ctx body bodyFuel source =
        .ok outcome :=
    runScoped_nonregular_of_runOpen model prim program hBody hMode
  have hStmt :
      Control.Stmt.run model prim program ctx bodyFuel (.block body) source =
        .ok (outcome, ctx) := by
    unfold Control.Stmt.run
    rw [hScoped]
    rfl
  exact
    runOpen_singleton_of_run model prim program hStmt

theorem runOpen_append_nonregular_exists {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program) :
    ∀ (left right : List Stmt) (ctx : Source.Ctx) (source : σ)
      (outcome : Outcome σ) (runCtx : Source.Ctx),
      (∃ fuel,
        Control.Block.runOpen model prim program ctx fuel
            { stmts := left } source =
          .ok (outcome, runCtx)) →
      outcome.mode ≠ .regular →
      ∃ fuel,
        Control.Block.runOpen model prim program ctx fuel
            { stmts := left ++ right } source =
          .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx source outcome runCtx hLeft hMode
      rcases hLeft with ⟨fuel, hLeft⟩
      rcases runOpen_nil_ok model prim program hLeft with
        ⟨hOutcome, _hCtx⟩
      rw [hOutcome] at hMode
      simp [Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hMode
  | cons stmt rest ih =>
      intro right ctx source outcome runCtx hLeft hMode
      rcases hLeft with ⟨fuel, hLeft⟩
      cases fuel with
      | zero =>
          simp [Control.Block.runOpen, Source.invalid,
            Structured.invalid] at hLeft
      | succ fuel =>
          rcases
              runOpen_cons_cases model prim program
                (fuel := fuel) hLeft with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨afterStmt, stmtCtx, hStmt, hRest⟩
            obtain ⟨tailFuel, hTail⟩ :=
              ih right stmtCtx afterStmt outcome runCtx
                ⟨fuel, hRest⟩ hMode
            simpa [List.cons_append] using
              runOpen_cons_regular_exists model prim program
                hStmt hTail
          · rcases hNonregular with
              ⟨headOutcome, headCtx, hHead, hHeadMode,
                hOutcome, hCtx⟩
            subst outcome
            subst runCtx
            exact
              ⟨fuel + 1,
                by
                  simpa [List.cons_append] using
                    runOpen_cons_nonregular model prim program
                      (rest := rest ++ right) hHead hHeadMode⟩

/--
Appending unreachable statements preserves the exact fuel of a nonregular
open-block execution.
-/
theorem runOpen_append_nonregular_at_same {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program) :
    ∀ (left right : List Stmt) (ctx : Source.Ctx) (source : σ)
      (outcome : Outcome σ) (runCtx : Source.Ctx) (fuel : Nat),
      Control.Block.runOpen model prim program ctx fuel
          { stmts := left } source =
        .ok (outcome, runCtx) →
      outcome.mode ≠ .regular →
      Control.Block.runOpen model prim program ctx fuel
          { stmts := left ++ right } source =
        .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx source outcome runCtx fuel hLeft hMode
      rcases runOpen_nil_ok model prim program hLeft with
        ⟨hOutcome, _hCtx⟩
      rw [hOutcome] at hMode
      simp [Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hMode
  | cons stmt rest ih =>
      intro right ctx source outcome runCtx runFuel hLeft hMode
      cases runFuel with
      | zero =>
          simp [Control.Block.runOpen, Source.invalid,
            Structured.invalid] at hLeft
      | succ fuel =>
          rcases
              runOpen_cons_cases model prim program
                (fuel := fuel) hLeft with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨afterStmt, stmtCtx, hStmt, hRest⟩
            have hTail :=
              ih right stmtCtx afterStmt outcome runCtx fuel
                hRest hMode
            simpa [Control.Block.runOpen, hStmt, hTail,
              Outcome.regular,
              Locals.Source.Effectful.Outcome.regular]
          · rcases hNonregular with
              ⟨headOutcome, headCtx, hHead, hHeadMode,
                hOutcome, hCtx⟩
            subst outcome
            subst runCtx
            simpa [List.cons_append] using
              runOpen_cons_nonregular model prim program
                (rest := rest ++ right) hHead hHeadMode

/--
Execute the compiler-generated Yul loop guard when the source condition is
zero. The condition preamble runs normally, `iszero` selects the synthetic
`break`, and the remaining lowered body is unreachable.
-/
theorem runScoped_forGuard_break_exists {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {bodyBase condCtx : Source.Ctx}
    {pre : List Stmt} {cond : Functions.Expr 1}
    {rest : List Stmt} {source afterPre afterEval : σ}
    {value : Word} {breakScope : List Name}
    (hPre :
      ∃ fuel,
        Control.Block.runOpen model prim program bodyBase fuel
            { stmts := pre } source =
          .ok (Outcome.regular afterPre, condCtx))
    (hEval :
      Expr.eval model prim cond afterPre =
        .ok (afterEval, [value]))
    (hIszero :
      prim.eval .iszero afterEval [value] =
        .ok (afterEval, [EvmYul.UInt256.isZero value]))
    (hZero : value = EvmYul.UInt256.ofNat 0)
    (hBreakScope : condCtx.breakScope? = some breakScope) :
    ∃ fuel,
      Control.Block.runScoped model prim program bodyBase
          { stmts :=
              pre ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                  { stmts := [.brk] } ::
                rest }
          fuel source =
        .ok (Outcome.brk (model.restrictTo breakScope afterEval)) := by
  have hGuard :
      Expr.evalCondition model prim
          (.prim .iszero (Locals.ExprSeq.cons cond .nil)) afterPre =
        .ok (afterEval, true) :=
    Expr.evalCondition_iszero_true_of_eval_singleton
      model prim hEval hIszero hZero
  have hBreakStmt :
      Control.Stmt.run model prim program condCtx 1 .brk afterEval =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) :=
    Stmt.run_brk_of_scope model prim program hBreakScope
  obtain ⟨breakOpenFuel, hBreakOpen⟩ :=
    runOpen_singleton_of_run model prim program hBreakStmt
  have hBreakScoped :
      Control.Block.runScoped model prim program condCtx
          { stmts := [.brk] } breakOpenFuel afterEval =
        .ok (Outcome.brk (model.restrictTo breakScope afterEval)) :=
    runScoped_nonregular_of_runOpen model prim program hBreakOpen (by simp)
  have hIfStmt :
      Control.Stmt.run model prim program condCtx (breakOpenFuel + 1)
          (.if_
            (.prim .iszero (Locals.ExprSeq.cons cond .nil))
            { stmts := [.brk] })
          afterPre =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) :=
    Stmt.run_if_true_of_eval model prim program hGuard hBreakScoped
  have hGuardTail :
      Control.Block.runOpen model prim program condCtx
          (breakOpenFuel + 2)
          { stmts :=
              .if_
                  (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                  { stmts := [.brk] } ::
                rest }
          afterPre =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) :=
    runOpen_cons_nonregular model prim program hIfStmt (by simp)
  obtain ⟨openFuel, hOpen⟩ :=
    runOpen_append_regular_exists model prim program
      pre
      (.if_
          (.prim .iszero (Locals.ExprSeq.cons cond .nil))
          { stmts := [.brk] } ::
        rest)
      bodyBase condCtx source afterPre
      (Outcome.brk (model.restrictTo breakScope afterEval))
      condCtx hPre ⟨breakOpenFuel + 2, hGuardTail⟩
  exact
    ⟨openFuel,
      runScoped_nonregular_of_runOpen model prim program hOpen (by simp)⟩

/--
Execute the compiler-generated false loop guard at an explicit additive fuel
budget. Five units cover the synthetic `break`, `if`, and open-block wrappers.
-/
theorem runScoped_forGuard_break_at_add_five {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {bodyBase condCtx : Source.Ctx}
    {pre : List Stmt} {cond : Functions.Expr 1}
    {rest : List Stmt} {source afterPre afterEval : σ}
    {value : Word} {breakScope : List Name} {preFuel : Nat}
    (hPre :
      Control.Block.runOpen model prim program bodyBase preFuel
          { stmts := pre } source =
        .ok (Outcome.regular afterPre, condCtx))
    (hEval :
      Expr.eval model prim cond afterPre =
        .ok (afterEval, [value]))
    (hIszero :
      prim.eval .iszero afterEval [value] =
        .ok (afterEval, [EvmYul.UInt256.isZero value]))
    (hZero : value = EvmYul.UInt256.ofNat 0)
    (hBreakScope : condCtx.breakScope? = some breakScope) :
    Control.Block.runScoped model prim program bodyBase
        { stmts :=
            pre ++
              .if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] } ::
              rest }
        (preFuel + 5) source =
      .ok (Outcome.brk (model.restrictTo breakScope afterEval)) := by
  have hGuard :
      Expr.evalCondition model prim
          (.prim .iszero (Locals.ExprSeq.cons cond .nil)) afterPre =
        .ok (afterEval, true) :=
    Expr.evalCondition_iszero_true_of_eval_singleton
      model prim hEval hIszero hZero
  have hBreakStmt :
      Control.Stmt.run model prim program condCtx 1 .brk afterEval =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) :=
    Stmt.run_brk_of_scope model prim program hBreakScope
  have hBreakOpen :
      Control.Block.runOpen model prim program condCtx 3
          { stmts := [.brk] } afterEval =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) := by
    simpa using
      runOpen_singleton_of_run_at_add_two model prim program hBreakStmt
  have hBreakScoped :
      Control.Block.runScoped model prim program condCtx
          { stmts := [.brk] } 3 afterEval =
        .ok (Outcome.brk (model.restrictTo breakScope afterEval)) :=
    runScoped_nonregular_of_runOpen model prim program hBreakOpen (by simp)
  have hIfStmt :
      Control.Stmt.run model prim program condCtx 4
          (.if_
            (.prim .iszero (Locals.ExprSeq.cons cond .nil))
            { stmts := [.brk] })
          afterPre =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) :=
    Stmt.run_if_true_of_eval model prim program hGuard hBreakScoped
  have hGuardTail :
      Control.Block.runOpen model prim program condCtx 5
          { stmts :=
              .if_
                  (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                  { stmts := [.brk] } ::
                rest }
          afterPre =
        .ok
          (Outcome.brk (model.restrictTo breakScope afterEval), condCtx) := by
    simpa using
      runOpen_cons_nonregular model prim program hIfStmt (by simp)
  have hOpen :=
    runOpen_append_regular_at_add model prim program
      pre
      (.if_
          (.prim .iszero (Locals.ExprSeq.cons cond .nil))
          { stmts := [.brk] } ::
        rest)
      bodyBase condCtx source afterPre
      (Outcome.brk (model.restrictTo breakScope afterEval))
      condCtx preFuel 5 hPre hGuardTail
  exact
    runScoped_nonregular_of_runOpen model prim program hOpen (by simp)

/--
Execute the compiler-generated Yul loop guard when the source condition is
nonzero, then continue with an arbitrary checked body run.

The condition preamble runs normally, `iszero` makes the synthetic `if` a
regular no-op, and the caller-owned body semantics supplies the remaining
open-block execution.
-/
theorem runOpen_forGuard_body_exists {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {bodyBase condCtx finalCtx : Source.Ctx}
    {pre : List Stmt} {cond : Functions.Expr 1}
    {rest : List Stmt} {source afterPre afterEval : σ}
    {value : Word} {outcome : Outcome σ}
    (hPre :
      ∃ fuel,
        Control.Block.runOpen model prim program bodyBase fuel
            { stmts := pre } source =
          .ok (Outcome.regular afterPre, condCtx))
    (hEval :
      Expr.eval model prim cond afterPre =
        .ok (afterEval, [value]))
    (hIszero :
      prim.eval .iszero afterEval [value] =
        .ok (afterEval, [EvmYul.UInt256.isZero value]))
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0)
    (hBody :
      ∃ fuel,
        Control.Block.runOpen model prim program condCtx fuel
            { stmts := rest } afterEval =
          .ok (outcome, finalCtx)) :
    ∃ fuel,
      Control.Block.runOpen model prim program bodyBase
          fuel
          { stmts :=
              pre ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                  { stmts := [.brk] } ::
                rest }
          source =
        .ok (outcome, finalCtx) := by
  have hGuard :
      Expr.evalCondition model prim
          (.prim .iszero (Locals.ExprSeq.cons cond .nil)) afterPre =
        .ok (afterEval, false) :=
    Expr.evalCondition_iszero_false_of_eval_singleton
      model prim hEval hIszero hNonzero
  have hIfStmt :
      Control.Stmt.run model prim program condCtx 1
          (.if_
            (.prim .iszero (Locals.ExprSeq.cons cond .nil))
            { stmts := [.brk] })
          afterPre =
        .ok (Outcome.regular afterEval, condCtx) :=
    Stmt.run_if_false_of_eval model prim program hGuard
  obtain ⟨ifFuel, hIfOpen⟩ :=
    runOpen_singleton_of_run model prim program hIfStmt
  obtain ⟨guardBodyFuel, hGuardBody⟩ :=
    runOpen_append_regular_exists model prim program
      [(.if_
        (.prim .iszero (Locals.ExprSeq.cons cond .nil))
        { stmts := [.brk] })]
      rest condCtx condCtx afterPre afterEval outcome finalCtx
      ⟨ifFuel, hIfOpen⟩ hBody
  simpa using
    runOpen_append_regular_exists model prim program
      pre
      (.if_
          (.prim .iszero (Locals.ExprSeq.cons cond .nil))
          { stmts := [.brk] } ::
        rest)
      bodyBase condCtx source afterPre outcome finalCtx
      hPre ⟨guardBodyFuel, hGuardBody⟩

/--
Execute the compiler-generated true loop guard followed by its body at an
explicit additive fuel budget. Three units cover the synthetic `if` and
singleton open-block wrapper.
-/
theorem runOpen_forGuard_body_at_add_three {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Program)
    {bodyBase condCtx finalCtx : Source.Ctx}
    {pre : List Stmt} {cond : Functions.Expr 1}
    {rest : List Stmt} {source afterPre afterEval : σ}
    {value : Word} {outcome : Outcome σ}
    {preFuel bodyFuel : Nat}
    (hPre :
      Control.Block.runOpen model prim program bodyBase preFuel
          { stmts := pre } source =
        .ok (Outcome.regular afterPre, condCtx))
    (hEval :
      Expr.eval model prim cond afterPre =
        .ok (afterEval, [value]))
    (hIszero :
      prim.eval .iszero afterEval [value] =
        .ok (afterEval, [EvmYul.UInt256.isZero value]))
    (hNonzero : value ≠ EvmYul.UInt256.ofNat 0)
    (hBody :
      Control.Block.runOpen model prim program condCtx bodyFuel
          { stmts := rest } afterEval =
        .ok (outcome, finalCtx)) :
    Control.Block.runOpen model prim program bodyBase
        (preFuel + bodyFuel + 3)
        { stmts :=
            pre ++
              .if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] } ::
              rest }
        source =
      .ok (outcome, finalCtx) := by
  have hGuard :
      Expr.evalCondition model prim
          (.prim .iszero (Locals.ExprSeq.cons cond .nil)) afterPre =
        .ok (afterEval, false) :=
    Expr.evalCondition_iszero_false_of_eval_singleton
      model prim hEval hIszero hNonzero
  have hIfStmt :
      Control.Stmt.run model prim program condCtx 1
          (.if_
            (.prim .iszero (Locals.ExprSeq.cons cond .nil))
            { stmts := [.brk] })
          afterPre =
        .ok (Outcome.regular afterEval, condCtx) :=
    Stmt.run_if_false_of_eval model prim program hGuard
  have hIfOpen :
      Control.Block.runOpen model prim program condCtx 3
          { stmts :=
              [(.if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] })] }
          afterPre =
        .ok (Outcome.regular afterEval, condCtx) := by
    simpa using
      runOpen_singleton_of_run_at_add_two model prim program hIfStmt
  have hGuardBody :=
    runOpen_append_regular_at_add model prim program
      [(.if_
        (.prim .iszero (Locals.ExprSeq.cons cond .nil))
        { stmts := [.brk] })]
      rest condCtx condCtx afterPre afterEval outcome finalCtx
      3 bodyFuel hIfOpen hBody
  have hAll :=
    runOpen_append_regular_at_add model prim program
      pre
      (.if_
          (.prim .iszero (Locals.ExprSeq.cons cond .nil))
          { stmts := [.brk] } ::
        rest)
      bodyBase condCtx source afterPre outcome finalCtx
      preFuel (3 + bodyFuel) hPre hGuardBody
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

end Block

namespace Program

def runState {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (program : Functions.Program) (state : σ) :
    Except EVMException (Outcome σ) :=
  Control.Block.runScoped model prim program Source.Ctx.initial
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
abbrev PrimitiveSemantics := Effectful.Control.PrimitiveSemantics
abbrev Outcome := Effectful.Outcome

namespace ArgList

abbrev eval {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.ArgList.Control.eval model prim

end ArgList

namespace Block

abbrev runOpen {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.Control.Block.runOpen model prim

abbrev runScoped {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.Control.Block.runScoped model prim

end Block

namespace FunDef

abbrev runBody {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.Control.FunDef.runBody model prim

end FunDef

namespace Stmt

abbrev runForLoop {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.Control.Stmt.runForLoop model prim

abbrev run {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.Control.Stmt.run model prim

end Stmt

namespace Program

abbrev runState {M : Type → Type} [Monad M]
    [MonadExceptOf EVMException M]
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics M σ) :=
  Effectful.Control.Program.runState model prim

end Program

end Canonical
end Source
end Functions
end EvmCompiler
