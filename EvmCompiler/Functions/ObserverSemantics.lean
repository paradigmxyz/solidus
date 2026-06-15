import EvmCompiler.Functions.EffectSemantics
import EvmCompiler.Locals.ObserverSemantics

namespace EvmCompiler
namespace Functions
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace
abbrev State := Locals.ObserverSemantics.State
abbrev Outcome := Locals.Source.Effectful.Outcome
abbrev basicOpObserver? := Locals.ObserverSemantics.basicOpObserver?

def stateModel (transcript : Trace) :
    Functions.Source.Effectful.StateModel (State transcript) :=
  Locals.ObserverSemantics.stateModel transcript

@[simp] theorem stateModel_insert
    {transcript : Trace} (state : State transcript)
    (name : Functions.Name) (value : Assembly.Word) :
    (stateModel transcript).insert state name value =
      state.withSource (state.source.insert name value) := by
  rfl

@[simp] theorem stateModel_withVars
    {transcript : Trace} (state : State transcript)
    (vars : Locals.Source.Store) :
    (stateModel transcript).withVars state vars =
      state.withSource (state.source.withVars vars) := by
  rfl

def primitiveSemantics (transcript : Trace) :
    Functions.Source.Effectful.PrimitiveSemantics (State transcript) :=
  Locals.ObserverSemantics.primitiveSemantics transcript

mutual
  theorem expr_eval_vars_eq
      {transcript : Trace} {results : Nat}
      {expr : Functions.Expr results}
      {source final : State transcript} {values : List Assembly.Word}
      (hEval :
        Functions.Source.Effectful.Expr.eval
            (stateModel transcript) (primitiveSemantics transcript)
            expr source =
          .ok (final, values)) :
      final.source.vars = source.source.vars := by
    cases expr with
    | lit value =>
        simp [Functions.Source.Effectful.Expr.eval,
          Locals.Source.Effectful.Expr.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        rfl
    | var name =>
        cases hLookup : source.source.vars name with
        | none =>
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval, stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.vars,
              Functions.Source.invalid, Structured.invalid,
              hLookup] at hEval
        | some value =>
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval, stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.vars,
              hLookup] at hEval
            rcases hEval with ⟨rfl, rfl⟩
            rfl
    | code code =>
        simp [Functions.Source.Effectful.Expr.eval,
          Locals.Source.Effectful.Expr.eval,
          Functions.Source.invalid, Structured.invalid] at hEval
    | prim op args =>
        unfold Functions.Source.Effectful.Expr.eval at hEval
        unfold Locals.Source.Effectful.Expr.eval at hEval
        cases hArgs :
            Locals.Source.Effectful.Expr.ExprSeq.eval
              (stateModel transcript) (primitiveSemantics transcript)
              args source with
        | error err =>
            simp [hArgs] at hEval
        | ok argsResult =>
            rcases argsResult with ⟨afterArgs, argValues⟩
            simp only [hArgs, Bind.bind, Except.bind] at hEval
            have hPrimVars :
                final.source.vars = afterArgs.source.vars :=
              Locals.ObserverSemantics.primitiveSemantics_eval_vars_eq hEval
            exact hPrimVars.trans (exprSeq_eval_vars_eq hArgs)

  theorem exprSeq_eval_vars_eq
      {transcript : Trace} {results : Nat}
      {exprs : Locals.ExprSeq results}
      {source final : State transcript} {values : List Assembly.Word}
      (hEval :
        Locals.Source.Effectful.Expr.ExprSeq.eval
            (stateModel transcript) (primitiveSemantics transcript)
            exprs source =
          .ok (final, values)) :
      final.source.vars = source.source.vars := by
    cases exprs with
    | nil =>
        simp [Locals.Source.Effectful.Expr.ExprSeq.eval] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        rfl
    | @cons left right head tail =>
        unfold Locals.Source.Effectful.Expr.ExprSeq.eval at hEval
        cases hHead :
            Functions.Source.Effectful.Expr.eval
              (stateModel transcript) (primitiveSemantics transcript)
              head source with
        | error err =>
            simp [hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨afterHead, headValues⟩
            simp only [hHead, Bind.bind, Except.bind] at hEval
            cases hTail :
                Locals.Source.Effectful.Expr.ExprSeq.eval
                  (stateModel transcript) (primitiveSemantics transcript)
                  tail afterHead with
            | error err =>
                simp [hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨afterTail, tailValues⟩
                simp only [hTail, Bind.bind, Except.bind] at hEval
                rcases hEval with ⟨rfl, rfl⟩
                exact (exprSeq_eval_vars_eq hTail).trans
                  (expr_eval_vars_eq hHead)
end

theorem argList_eval_vars_eq
    {transcript : Trace}
    {args : List (Functions.Expr 1)}
    {source final : State transcript} {values : List Assembly.Word}
    (hEval :
      Functions.Source.Effectful.ArgList.eval
          (stateModel transcript) (primitiveSemantics transcript)
          args source =
        .ok (final, values)) :
    final.source.vars = source.source.vars := by
  induction args generalizing source final values with
  | nil =>
      simp [Functions.Source.Effectful.ArgList.eval] at hEval
      rcases hEval with ⟨rfl, rfl⟩
      rfl
  | cons head rest ih =>
      unfold Functions.Source.Effectful.ArgList.eval at hEval
      cases hHead :
          Functions.Source.Effectful.Expr.evalOne
            (stateModel transcript) (primitiveSemantics transcript)
            head source with
      | error err =>
          simp [hHead] at hEval
      | ok headResult =>
          rcases headResult with ⟨afterHead, headValue⟩
          simp only [hHead, Bind.bind, Except.bind] at hEval
          cases hRest :
              Functions.Source.Effectful.ArgList.eval
                (stateModel transcript) (primitiveSemantics transcript)
                rest afterHead with
          | error err =>
              simp [hRest] at hEval
          | ok restResult =>
              rcases restResult with ⟨afterRest, restValues⟩
              simp only [hRest, Bind.bind, Except.bind] at hEval
              rcases hEval with ⟨rfl, rfl⟩
              have hHeadEval :
                  Functions.Source.Effectful.Expr.eval
                      (stateModel transcript) (primitiveSemantics transcript)
                      head source =
                    .ok (afterHead, [headValue]) := by
                unfold Functions.Source.Effectful.Expr.evalOne at hHead
                unfold Locals.Source.Effectful.Expr.evalOne at hHead
                cases hExpr :
                    Functions.Source.Effectful.Expr.eval
                      (stateModel transcript) (primitiveSemantics transcript)
                      head source with
                | error err =>
                    simp [hExpr] at hHead
                | ok result =>
                    rcases result with ⟨stateAfterExpr, exprValues⟩
                    cases exprValues with
                    | nil =>
                        simp [hExpr, Functions.Source.invalid,
                          Structured.invalid] at hHead
                    | cons value tail =>
                        cases tail with
                        | nil =>
                            simp [hExpr] at hHead
                            rcases hHead with ⟨rfl, rfl⟩
                            rfl
                        | cons second remaining =>
                            simp [hExpr, Functions.Source.invalid,
                              Structured.invalid] at hHead
              exact (ih hRest).trans (expr_eval_vars_eq hHeadEval)

theorem primitiveSemantics_eval_observer
    {transcript : Trace} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver}
    {state state' : State transcript} {value : Assembly.Word}
    (hObserver : basicOpObserver? op = some kind)
    (hConsume :
      Simulation.ResourceReplay.consume? kind state =
        some (value, state')) :
    (primitiveSemantics transcript).eval op state [] =
      .ok (state', [value]) := by
  simp [primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    basicOpObserver?, hObserver, hConsume]

theorem primitiveSemantics_eval_observer_parts
    {transcript : Trace} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver}
    {state final : State transcript} {outputs : List Assembly.Word}
    (hObserver : basicOpObserver? op = some kind)
    (hEval :
      (primitiveSemantics transcript).eval op state [] =
        .ok (final, outputs)) :
    ∃ value,
      outputs = [value] ∧
      Simulation.ResourceReplay.consume? kind state =
        some (value, final) := by
  unfold primitiveSemantics at hEval
  unfold Locals.ObserverSemantics.primitiveSemantics at hEval
  simp only [basicOpObserver?, hObserver] at hEval
  cases hConsume :
      Simulation.ResourceReplay.consume? kind state with
  | none =>
      simp [hConsume, Structured.invalid] at hEval
  | some consumed =>
      rcases consumed with ⟨value, state'⟩
      simp [hConsume] at hEval
      rcases hEval with ⟨rfl, rfl⟩
      exact ⟨value, rfl, by simpa [hConsume]⟩

theorem primitiveSemantics_eval_observer_values_eq_nil
    {transcript : Trace} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver}
    {state final : State transcript} {values outputs : List Assembly.Word}
    (hObserver : basicOpObserver? op = some kind)
    (hEval :
      (primitiveSemantics transcript).eval op state values =
        .ok (final, outputs)) :
    values = [] := by
  unfold primitiveSemantics at hEval
  unfold Locals.ObserverSemantics.primitiveSemantics at hEval
  simp only [basicOpObserver?, hObserver] at hEval
  cases values with
  | nil => rfl
  | cons head tail =>
      simp [Structured.invalid] at hEval

theorem primitiveSemantics_eval_nonObserver
    {transcript : Trace} {op : Structured.BasicOp}
    {state : State transcript} {values outputs : List Assembly.Word}
    {shared : EvmYul.SharedState .EVM}
    (hObserver : basicOpObserver? op = none)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          op state.source.shared values =
        .ok (shared, outputs)) :
    (primitiveSemantics transcript).eval op state values =
      .ok
        (state.withSource (state.source.withShared shared), outputs) := by
  simp [primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    basicOpObserver?, hObserver, hEval,
    Simulation.ResourceReplay.State.withSource]

theorem primitiveSemantics_eval_nonObserver_parts
    {transcript : Trace} {op : Structured.BasicOp}
    {state final : State transcript} {values outputs : List Assembly.Word}
    (hObserver : basicOpObserver? op = none)
    (hEval :
      (primitiveSemantics transcript).eval op state values =
        .ok (final, outputs)) :
    ∃ shared,
      Locals.Source.PrimitiveSemantics.structured.eval
          op state.source.shared values =
        .ok (shared, outputs) ∧
      final =
        state.withSource (state.source.withShared shared) := by
  unfold primitiveSemantics at hEval
  unfold Locals.ObserverSemantics.primitiveSemantics at hEval
  simp only [basicOpObserver?, hObserver] at hEval
  cases hPrimitive :
      Locals.Source.PrimitiveSemantics.structured.eval
        op state.source.shared values with
  | error err =>
      simp [hPrimitive] at hEval
  | ok result =>
      rcases result with ⟨shared, rawOutputs⟩
      simp [hPrimitive] at hEval
      rcases hEval with ⟨hFinal, hOutputs⟩
      subst final
      subst outputs
      exact ⟨shared, by simpa [hPrimitive], rfl⟩

theorem expr_eval_gas
    {transcript : Trace} {state state' : State transcript}
    {value : Assembly.Word}
    (hConsume :
      Simulation.ResourceReplay.consume? .gas state =
        some (value, state')) :
    Functions.Source.Effectful.Expr.eval
        (stateModel transcript) (primitiveSemantics transcript)
        (.prim .gas .nil : Functions.Expr 1) state =
      .ok (state', [value]) := by
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    primitiveSemantics_eval_observer (op := .gas) (by rfl) hConsume]

theorem expr_eval_msize
    {transcript : Trace} {state state' : State transcript}
    {value : Assembly.Word}
    (hConsume :
      Simulation.ResourceReplay.consume? .msize state =
        some (value, state')) :
    Functions.Source.Effectful.Expr.eval
        (stateModel transcript) (primitiveSemantics transcript)
        (.prim .msize .nil : Functions.Expr 1) state =
      .ok (state', [value]) := by
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    primitiveSemantics_eval_observer (op := .msize) (by rfl) hConsume]

theorem expr_evalOne_gas
    {transcript : Trace} {state state' : State transcript}
    {value : Assembly.Word}
    (hConsume :
      Simulation.ResourceReplay.consume? .gas state =
        some (value, state')) :
    Functions.Source.Effectful.Expr.evalOne
        (stateModel transcript) (primitiveSemantics transcript)
        (.prim .gas .nil : Functions.Expr 1) state =
      .ok (state', value) := by
  unfold Functions.Source.Effectful.Expr.evalOne
  unfold Locals.Source.Effectful.Expr.evalOne
  have hEval :
      Locals.Source.Effectful.Expr.eval
          (stateModel transcript) (primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) state =
        .ok (state', [value]) :=
    expr_eval_gas hConsume
  rw [hEval]
  simp [Bind.bind, Except.bind]

theorem expr_evalOne_msize
    {transcript : Trace} {state state' : State transcript}
    {value : Assembly.Word}
    (hConsume :
      Simulation.ResourceReplay.consume? .msize state =
        some (value, state')) :
    Functions.Source.Effectful.Expr.evalOne
        (stateModel transcript) (primitiveSemantics transcript)
        (.prim .msize .nil : Functions.Expr 1) state =
      .ok (state', value) := by
  unfold Functions.Source.Effectful.Expr.evalOne
  unfold Locals.Source.Effectful.Expr.evalOne
  have hEval :
      Locals.Source.Effectful.Expr.eval
          (stateModel transcript) (primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) state =
        .ok (state', [value]) :=
    expr_eval_msize hConsume
  rw [hEval]
  simp [Bind.bind, Except.bind]

theorem stmt_run_let_gas
    {transcript : Trace} {state state' : State transcript}
    {value : Assembly.Word}
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (name : Functions.Name)
    (hConsume :
      Simulation.ResourceReplay.consume? .gas state =
        some (value, state')) :
    Functions.Source.Effectful.Stmt.run
        (stateModel transcript) (primitiveSemantics transcript)
        program ctx fuel (.let_ name (.prim .gas .nil : Functions.Expr 1))
        state =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          (state'.withSource (state'.source.insert name value)),
          { ctx with scope := name :: ctx.scope }) := by
  unfold Functions.Source.Effectful.Stmt.run
  change
    (do
      let (stateAfterValue, value') ←
        Functions.Source.Effectful.Expr.evalOne
          (stateModel transcript) (primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) state
      .ok
        (Functions.Source.Effectful.Outcome.regular
          ((stateModel transcript).insert stateAfterValue name value'),
          { ctx with scope := name :: ctx.scope })) =
      _
  rw [expr_evalOne_gas hConsume]
  rfl

theorem stmt_run_let_msize
    {transcript : Trace} {state state' : State transcript}
    {value : Assembly.Word}
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (name : Functions.Name)
    (hConsume :
      Simulation.ResourceReplay.consume? .msize state =
        some (value, state')) :
    Functions.Source.Effectful.Stmt.run
        (stateModel transcript) (primitiveSemantics transcript)
        program ctx fuel (.let_ name (.prim .msize .nil : Functions.Expr 1))
        state =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          (state'.withSource (state'.source.insert name value)),
          { ctx with scope := name :: ctx.scope }) := by
  unfold Functions.Source.Effectful.Stmt.run
  change
    (do
      let (stateAfterValue, value') ←
        Functions.Source.Effectful.Expr.evalOne
          (stateModel transcript) (primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) state
      .ok
        (Functions.Source.Effectful.Outcome.regular
          ((stateModel transcript).insert stateAfterValue name value'),
          { ctx with scope := name :: ctx.scope })) =
      _
  rw [expr_evalOne_msize hConsume]
  rfl

namespace Program

def runState (fuel : Nat) (program : Functions.Program)
    {transcript : Trace} (state : State transcript) :
    Except EVMException (Outcome (State transcript)) :=
  Functions.Source.Effectful.Program.runState
    (stateModel transcript) (primitiveSemantics transcript)
    fuel program state

end Program

@[simp] theorem stmt_run_let_gas_cons
    (fuel : Nat) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (source : Locals.Source.State)
    (name : Functions.Name) (value : Assembly.Word) (rest : Trace) :
    Functions.Source.Effectful.Stmt.run
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        program ctx fuel
        (.let_ name (.prim .gas .nil : Functions.Expr 1))
        { source := source } =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          { source := source.insert name value, cursor := 1 },
          { ctx with scope := name :: ctx.scope }) := by
  simp [Functions.Source.Effectful.Stmt.run,
    Functions.Source.Effectful.Expr.evalOne,
    Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Functions.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.StateModel.insert,
    Locals.Source.State.insert,
    stateModel, Locals.ObserverSemantics.stateModel,
    Simulation.ResourceReplay.State.withSource,
    Simulation.ResourceReplay.consume?]

@[simp] theorem runBody_let_gas_cons
    (fuel : Nat) (program : Functions.Program)
    (source : Locals.Source.State) (functionName localName : Functions.Name)
    (value : Assembly.Word) (rest : Trace) :
    Functions.Source.Effectful.FunDef.runBody
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        program
        { name := functionName
          params := []
          returns := []
          body :=
            { stmts :=
                [.let_ localName
                  (.prim .gas .nil : Functions.Expr 1)] } }
        [] fuel.succ.succ.succ { source := source } =
      .ok
        (.returned
          { source :=
              { shared := source.shared,
                vars :=
                  Locals.Source.Store.insert
                    Locals.Source.Store.empty localName value },
            cursor := 1 }
          []) := by
  simp [Functions.Source.Effectful.FunDef.runBody,
    Functions.Source.Effectful.Block.runOpen,
    Functions.Source.Effectful.Stmt.run,
    Functions.Source.Effectful.Expr.evalOne,
    Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    Functions.Source.Store.insertMany, Functions.Source.Store.initReturns,
    Functions.Source.Store.lookupMany,
    primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Functions.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.StateModel.insert,
    Locals.Source.State.insert,
    stateModel, Locals.ObserverSemantics.stateModel,
    Simulation.ResourceReplay.State.withSource,
    Simulation.ResourceReplay.consume?]

@[simp] theorem stmt_run_call_let_gas_cons
    (fuel : Nat) (source : Locals.Source.State)
    (functionName localName : Functions.Name)
    (value : Assembly.Word) (rest : Trace) :
    let fn : Functions.FunDef :=
      { name := functionName
        params := []
        returns := []
        body :=
          { stmts :=
              [.let_ localName
                (.prim .gas .nil : Functions.Expr 1)] } }
    let program : Functions.Program :=
      { functions := [fn], body := { stmts := [] } }
    Functions.Source.Effectful.Stmt.run
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        program Functions.Source.Ctx.initial fuel.succ.succ.succ.succ
        (.call [] functionName []) { source := source } =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          { source := source, cursor := 1 },
          Functions.Source.Ctx.initial) := by
  cases source
  simp [Functions.Source.Effectful.Stmt.run,
    Functions.Source.Effectful.ArgList.eval,
    Functions.Source.FunList.find?,
    Functions.Source.Effectful.FunDef.runBody,
    Functions.Source.Effectful.Block.runOpen,
    Functions.Source.Effectful.Expr.evalOne,
    Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    Functions.Source.Store.insertMany, Functions.Source.Store.initReturns,
    Functions.Source.Store.lookupMany, Functions.Source.Store.assignMany,
    primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Functions.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.StateModel.vars,
    Locals.Source.Effectful.StateModel.insert,
    Locals.Source.State.insert,
    stateModel, Locals.ObserverSemantics.stateModel,
    Simulation.ResourceReplay.State.withSource,
    Simulation.ResourceReplay.consume?]

end ObserverSemantics
end Functions
end EvmCompiler
