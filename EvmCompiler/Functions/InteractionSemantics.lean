import EvmCompiler.Functions.EffectSemantics
import EvmCompiler.Locals.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace InteractionSemantics

abbrev Open (α : Type) :=
  Simulation.Interaction EVMException α

abbrev State := Locals.InteractionSemantics.State
abbrev Outcome := Functions.Source.Effectful.Outcome State
abbrev CallResult := Functions.Source.Effectful.CallResult State

def stateModel : Functions.Source.Canonical.StateModel State :=
  Locals.InteractionSemantics.stateModel

def primitiveSemantics :
    Functions.Source.Canonical.PrimitiveSemantics Open State :=
  Locals.InteractionSemantics.primitiveSemantics

namespace Expr

def openEval {results : Nat} (expr : Functions.Expr results)
    (state : State) : Open (State × List Word) :=
  Locals.InteractionSemantics.Expr.openEval expr state

def openEvalOne (expr : Functions.Expr 1)
    (state : State) : Open (State × Word) :=
  Locals.InteractionSemantics.Expr.openEvalOne expr state

def openEvalCondition (expr : Functions.Expr 1)
    (state : State) : Open (State × Bool) :=
  Locals.InteractionSemantics.Expr.openEvalCondition expr state

abbrev OpenSupported {results : Nat} (expr : Functions.Expr results) : Prop :=
  Locals.InteractionSemantics.Expr.OpenSupported expr

end Expr

namespace ExprSeq

def openEval {results : Nat} (exprs : Locals.ExprSeq results)
    (state : State) : Open (State × List Word) :=
  Locals.InteractionSemantics.ExprSeq.openEval exprs state

abbrev OpenSupported {results : Nat}
    (exprs : Locals.ExprSeq results) : Prop :=
  Locals.InteractionSemantics.ExprSeq.OpenSupported exprs

end ExprSeq

namespace ArgList

def openEval (args : List (Functions.Expr 1)) (state : State) :
    Open (State × List Word) :=
  Functions.Source.Canonical.ArgList.eval
    stateModel primitiveSemantics args state

def OpenSupported (args : List (Functions.Expr 1)) : Prop :=
  ∀ expr, expr ∈ args →
    Locals.InteractionSemantics.Expr.OpenSupported expr

/-- Ordered function arguments preserve the caller's local bindings on every
open-world branch. -/
theorem openEval_vars_eq (args : List (Functions.Expr 1)) (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval args state) := by
  induction args generalizing state with
  | nil =>
      exact .done rfl
  | cons arg rest ih =>
      unfold openEval Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval
      apply Simulation.Interaction.AllDone.bind
        (Locals.InteractionSemantics.Expr.openEvalOne_vars_eq arg state)
      · intro _ _
        trivial
      · intro headResult hHead
        rcases headResult with ⟨afterHead, value⟩
        apply Simulation.Interaction.AllDone.bind (ih afterHead)
        · intro _ _
          trivial
        · intro tailResult hTail
          rcases tailResult with ⟨afterTail, values⟩
          exact .done (hTail.trans hHead)

end ArgList

namespace Block

def openRun (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (block : Functions.Block) (state : State) :
    Open (Outcome × Functions.Source.Ctx) :=
  Functions.Source.Canonical.Block.runOpen
    stateModel primitiveSemantics program ctx fuel block state

def openRunScoped (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (block : Functions.Block)
    (fuel : Nat) (state : State) : Open Outcome :=
  Functions.Source.Canonical.Block.runScoped
    stateModel primitiveSemantics program ctx block fuel state

theorem openRun_terminal_cons
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (kind : Assembly.HaltKind)
    (rest : List Functions.Stmt) (state : State) :
    openRun program ctx (fuel + 1)
        { stmts := .terminal kind :: rest } state =
      Functions.Source.Canonical.Stmt.run stateModel primitiveSemantics
        program ctx fuel (.terminal kind) state := by
  unfold openRun Functions.Source.Canonical.Block.runOpen
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Block.runOpen
    Functions.Source.Effectful.Control.Stmt.run
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (primitiveSemantics.terminal kind state [])
          (fun final =>
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.halt kind final, ctx)))
        (fun result =>
          match result.1.mode with
          | .regular =>
              Functions.Source.Effectful.Control.Block.runOpen stateModel
                primitiveSemantics program result.2 fuel
                { stmts := rest } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) =
      Simulation.Interaction.bind
        (primitiveSemantics.terminal kind state [])
        (fun final =>
          Simulation.Interaction.pure
            (Functions.Source.Effectful.Outcome.halt kind final, ctx))
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (primitiveSemantics.terminal kind state []))
  intro final _
  rfl

theorem openRun_terminalArgs_cons
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    (rest : List Functions.Stmt) (state : State) :
    openRun program ctx (fuel + 1)
        { stmts := .terminalArgs kind args :: rest } state =
      Functions.Source.Canonical.Stmt.run stateModel primitiveSemantics
        program ctx fuel (.terminalArgs kind args) state := by
  unfold openRun Functions.Source.Canonical.Block.runOpen
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Block.runOpen
    Functions.Source.Effectful.Control.Stmt.run
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Locals.Source.Effectful.Expr.Control.ExprSeq.eval stateModel
            primitiveSemantics args state)
          (fun result =>
            Simulation.Interaction.bind
              (primitiveSemantics.terminal kind result.1 result.2)
              (fun final =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.halt kind final,
                    ctx))))
        (fun result =>
          match result.1.mode with
          | .regular =>
              Functions.Source.Effectful.Control.Block.runOpen stateModel
                primitiveSemantics program result.2 fuel
                { stmts := rest } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) =
      Simulation.Interaction.bind
        (Locals.Source.Effectful.Expr.Control.ExprSeq.eval stateModel
          primitiveSemantics args state)
        (fun result =>
          Simulation.Interaction.bind
            (primitiveSemantics.terminal kind result.1 result.2)
            (fun final =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.halt kind final, ctx)))
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.Source.Effectful.Expr.Control.ExprSeq.eval stateModel
        primitiveSemantics args state))
  intro result _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (primitiveSemantics.terminal kind result.1 result.2))
  intro final _
  rfl

theorem openRunScoped_eq_bind
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (block : Functions.Block) (fuel : Nat) (state : State) :
    openRunScoped program ctx block fuel state =
      Simulation.Interaction.bind
        (openRun program ctx fuel block state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (result.1.state.restrictTo ctx.scope))
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure result.1) := by
  unfold openRunScoped openRun Functions.Source.Canonical.Block.runScoped
    Functions.Source.Canonical.Block.runOpen
    Functions.Source.Effectful.Control.Block.runScoped
  rfl

/-- Successful canonical block execution always has positive meta-fuel. -/
theorem successful_openRun_fuel_pos
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {block : Functions.Block} {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx fuel block state)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      unfold openRun Functions.Source.Canonical.Block.runOpen at hSuccess
      simp only [Functions.Source.Effectful.Control.Block.runOpen] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.OutOfFuel : EVMException) hSuccess)
  | succ fuel => omega

/-- One source statement followed by its exact residual block. -/
theorem openRun_cons
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (state : State) :
    openRun program ctx (fuel + 1) { stmts := stmt :: rest } state =
      Simulation.Interaction.bind
        (Functions.Source.Effectful.Control.Stmt.run
          stateModel primitiveSemantics program ctx fuel stmt state)
        (fun result =>
        match result.1.mode with
        | .regular =>
            Functions.Source.Effectful.Control.Block.runOpen
              stateModel primitiveSemantics program result.2 fuel
              { stmts := rest } result.1.state
        | .brk | .cont | .leave | .halt _ =>
            Simulation.Interaction.pure (result.1, ctx)) := by
  change
    Functions.Source.Effectful.Control.Block.runOpen
        stateModel primitiveSemantics program ctx (fuel + 1)
        { stmts := stmt :: rest } state = _
  rw [Nat.add_one]
  simp only [Functions.Source.Effectful.Control.Block.runOpen]
  change
    Simulation.Interaction.bind
        (Functions.Source.Effectful.Control.Stmt.run
          stateModel primitiveSemantics program ctx fuel stmt state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Functions.Source.Effectful.Control.Block.runOpen
                stateModel primitiveSemantics program result.2 fuel
                { stmts := rest } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) = _
  rfl

theorem openRun_leave_cons
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (rest : List Functions.Stmt) (state : State) :
    openRun program ctx (fuel + 1) { stmts := .leave :: rest } state =
      Functions.Source.Canonical.Stmt.run stateModel primitiveSemantics
        program ctx fuel .leave state := by
  rw [openRun_cons]
  unfold Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  cases hScope : ctx.leaveScope? with
  | none =>
      simp only [hScope]
      change Simulation.Interaction.bind
          (Simulation.Interaction.done
            (.error EvmYul.EVM.ExecutionException.InvalidInstruction)) _ =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.InvalidInstruction)
      rw [Simulation.Interaction.bind_done_error]
  | some scope =>
      simp only [hScope]
      let result :=
        (Functions.Source.Effectful.Outcome.leave
            (stateModel.restrictTo scope state),
          ctx)
      change Simulation.Interaction.bind
          ((pure result) : Open (Outcome × Functions.Source.Ctx)) _ =
        ((pure result) : Open (Outcome × Functions.Source.Ctx))
      change Simulation.Interaction.bind
          (Simulation.Interaction.done (.ok result)) _ =
        Simulation.Interaction.done (.ok result)
      rw [Simulation.Interaction.bind_done_ok]
      simp [result]
      rfl

/-- A successful nonempty block exposes a successful canonical head run. -/
theorem successful_openRun_cons_head
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx (fuel + 1) { stmts := stmt :: rest } state)) :
    Simulation.Interaction.Successful
      (Functions.Source.Effectful.Control.Stmt.run
        stateModel primitiveSemantics program ctx fuel stmt state) := by
  rw [openRun_cons] at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

/-- A nonzero-fuel empty source block is the regular identity. -/
theorem openRun_nil
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) :
    openRun program ctx (fuel + 1) { stmts := [] } state =
      (pure (Functions.Source.Effectful.Outcome.regular state, ctx) :
        Open (Outcome × Functions.Source.Ctx)) := by
  change
    Functions.Source.Effectful.Control.Block.runOpen
        stateModel primitiveSemantics program ctx (fuel + 1)
        { stmts := [] } state = _
  rw [Nat.add_one]
  simp only [Functions.Source.Effectful.Control.Block.runOpen]

/-- Executing an appended canonical Functions block factors through the left
block.  Regular completion continues with its resulting lexical context and
exact residual list fuel; abrupt completion restores the outer context and
skips the suffix. -/
theorem openRun_append (program : Functions.Program) :
    ∀ (left right : List Functions.Stmt) (ctx : Functions.Source.Ctx)
      (fuel : Nat) (state : State),
      openRun program ctx fuel { stmts := left ++ right } state =
        Simulation.Interaction.bind
          (openRun program ctx fuel { stmts := left } state)
          (fun result =>
            match result.1.mode with
            | .regular =>
                openRun program result.2 (fuel - left.length)
                  { stmts := right } result.1.state
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure result) := by
  intro left
  induction left with
  | nil =>
      intro right ctx fuel state
      cases fuel with
      | zero =>
          unfold openRun Functions.Source.Canonical.Block.runOpen
          simp only [Functions.Source.Effectful.Control.Block.runOpen]
          rfl
      | succ fuel =>
          simp only [List.nil_append, List.length_nil, Nat.sub_zero]
          rw [openRun_nil]
          rfl
  | cons stmt rest ih =>
      intro right ctx fuel state
      cases fuel with
      | zero =>
          unfold openRun Functions.Source.Canonical.Block.runOpen
          simp only [Functions.Source.Effectful.Control.Block.runOpen]
          rfl
      | succ fuel =>
          rw [show stmt :: rest ++ right =
              stmt :: (rest ++ right) by rfl,
            openRun_cons, openRun_cons]
          simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]
          rw [Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Functions.Source.Effectful.Control.Stmt.run
                stateModel primitiveSemantics program ctx fuel stmt state))
          intro outcome _
          cases hMode : outcome.1.mode with
          | regular =>
              simpa [hMode] using
                ih right outcome.2 fuel outcome.1.state
          | brk =>
              change
                Simulation.Interaction.pure (outcome.1, ctx) =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure (outcome.1, ctx)) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]
          | cont =>
              change
                Simulation.Interaction.pure (outcome.1, ctx) =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure (outcome.1, ctx)) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]
          | leave =>
              change
                Simulation.Interaction.pure (outcome.1, ctx) =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure (outcome.1, ctx)) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]
          | halt kind =>
              change
                Simulation.Interaction.pure (outcome.1, ctx) =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure (outcome.1, ctx)) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]

/-- Scoped execution of an appended canonical Functions block factors through
the left block while retaining the outer lexical restriction. -/
theorem openRunScoped_append (program : Functions.Program)
    (left right : List Functions.Stmt) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) :
    openRunScoped program ctx { stmts := left ++ right } fuel state =
      Simulation.Interaction.bind
        (openRun program ctx fuel { stmts := left } state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.bind
                (openRun program result.2 (fuel - left.length)
                  { stmts := right } result.1.state)
                (fun tail =>
                  match tail.1.mode with
                  | .regular =>
                      Simulation.Interaction.pure
                        (Functions.Source.Effectful.Outcome.regular
                          (tail.1.state.restrictTo ctx.scope))
                  | .brk | .cont | .leave | .halt _ =>
                      Simulation.Interaction.pure tail.1)
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure result.1) := by
  unfold openRunScoped Functions.Source.Canonical.Block.runScoped
    Functions.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.bind
        (openRun program ctx fuel { stmts := left ++ right } state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (result.1.state.restrictTo ctx.scope))
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure result.1) = _
  rw [openRun_append, Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (openRun program ctx fuel { stmts := left } state))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular => simp [hMode]
  | brk | cont | leave | halt =>
      unfold Simulation.Interaction.pure
      rw [Simulation.Interaction.bind_done_ok]
      simp [hMode]

end Block

namespace FunDef

def openRunBody (program : Functions.Program) (fn : Functions.FunDef)
    (args : List Word) (fuel : Nat) (state : State) : Open CallResult :=
  Functions.Source.Canonical.FunDef.runBody
    stateModel primitiveSemantics program fn args fuel state

/-- Successful canonical function execution has positive meta-fuel. -/
theorem successful_openRunBody_fuel_pos
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Word} {fuel : Nat} {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRunBody program fn args fuel state)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      unfold openRunBody Functions.Source.Canonical.FunDef.runBody at hSuccess
      simp only [Functions.Source.Effectful.Control.FunDef.runBody] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.OutOfFuel : EVMException) hSuccess)
  | succ fuel => omega

/-- Successful canonical function execution exposes the real initialized body
run one fuel level below it. -/
theorem successful_openRunBody_parts
    (program : Functions.Program) (fn : Functions.FunDef)
    (args : List Word) (fuel : Nat) (state : State)
    (hSuccess :
      Simulation.Interaction.Successful
        (openRunBody program fn args (fuel + 1) state)) :
    ∃ paramStore,
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore ∧
        Simulation.Interaction.Successful
          (Block.openRun program
            (Functions.Source.Effectful.FunDef.bodyCtx fn) fuel fn.body
            (stateModel.withSource state
              { shared := (stateModel.source state).shared
                vars := Functions.Source.Store.initReturns
                  fn.returns paramStore })) := by
  unfold openRunBody Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody at hSuccess
  cases hParams : Functions.Source.Store.insertMany fn.params args
      Locals.Source.Store.empty with
  | none =>
      have hPrefix := Simulation.Interaction.Successful.bind_left hSuccess
      simp only [hParams, Option.elim_none] at hPrefix
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hPrefix)
  | some paramStore =>
      refine ⟨paramStore, rfl, ?_⟩
      simp only [hParams, Option.elim_some,
        Simulation.Interaction.bind_done_ok] at hSuccess
      exact Simulation.Interaction.Successful.bind_left hSuccess

/-- Construct a canonical open returned function result from parameter
initialization, one completed body, and exact return lookup. -/
theorem openRunBody_returned_of_parts
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Word} {fuel : Nat} {state returnedState : State}
    {returnValues : List Word} {paramStore : Functions.Source.Store}
    {bodyOutcome : Outcome} {bodyCtx' : Functions.Source.Ctx}
    (hParams :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBody :
      Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) fuel fn.body
          (stateModel.withSource state
            { shared := (stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) =
        .done (.ok (bodyOutcome, bodyCtx')))
    (hMode : bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave)
    (hReturns :
      Functions.Source.Store.lookupMany fn.returns
          (stateModel.vars bodyOutcome.state) = some returnValues)
    (hState : bodyOutcome.state = returnedState) :
    openRunBody program fn args (fuel + 1) state =
      .done (.ok
        (Functions.Source.Effectful.CallResult.returned
          returnedState returnValues)) := by
  have hBody' :
      Functions.Source.Effectful.Control.Block.runOpen
          stateModel primitiveSemantics program
          { Functions.Source.Ctx.initial.withLeaveScope
              (fn.returns ++ fn.params) with
            scope := fn.returns ++ fn.params }
          fuel fn.body
          (stateModel.withSource state
            { shared := (stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) =
        .done (.ok (bodyOutcome, bodyCtx')) := by
    simpa [Functions.Source.Effectful.FunDef.bodyCtx] using hBody
  unfold openRunBody Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody
  rw [hParams]
  change
    Simulation.Interaction.bind
        (Functions.Source.Effectful.Control.Block.runOpen
          stateModel primitiveSemantics program
          { Functions.Source.Ctx.initial.withLeaveScope
              (fn.returns ++ fn.params) with
            scope := fn.returns ++ fn.params }
          fuel fn.body
          (stateModel.withSource state
            { shared := (stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore })) _ = _
  rw [hBody']
  rw [Simulation.Interaction.bind_done_ok]
  simp only
  rcases hMode with hMode | hMode
  · rw [hMode, hReturns, hState]
    rfl
  · rw [hMode, hReturns, hState]
    rfl

/-- Construct a canonical open halting function result from parameter
initialization and the actual open body execution. -/
theorem openRunBody_halted_of_parts
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Word} {fuel : Nat} {state haltedState : State}
    {kind : Assembly.HaltKind} {paramStore : Functions.Source.Store}
    {bodyCtx' : Functions.Source.Ctx}
    (hParams :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBody :
      Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) fuel fn.body
          (stateModel.withSource state
            { shared := (stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) =
        .done (.ok
          (Functions.Source.Effectful.Outcome.halt kind haltedState,
            bodyCtx'))) :
    openRunBody program fn args (fuel + 1) state =
      .done (.ok
        (Functions.Source.Effectful.CallResult.halted kind haltedState)) := by
  have hBody' :
      Functions.Source.Effectful.Control.Block.runOpen
          stateModel primitiveSemantics program
          { Functions.Source.Ctx.initial.withLeaveScope
              (fn.returns ++ fn.params) with
            scope := fn.returns ++ fn.params }
          fuel fn.body
          (stateModel.withSource state
            { shared := (stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) =
        .done (.ok
          (Functions.Source.Effectful.Outcome.halt kind haltedState,
            bodyCtx')) := by
    simpa [Functions.Source.Effectful.FunDef.bodyCtx] using hBody
  unfold openRunBody Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody
  rw [hParams]
  change
    Simulation.Interaction.bind
        (Functions.Source.Effectful.Control.Block.runOpen
          stateModel primitiveSemantics program
          { Functions.Source.Ctx.initial.withLeaveScope
              (fn.returns ++ fn.params) with
            scope := fn.returns ++ fn.params }
          fuel fn.body
          (stateModel.withSource state
            { shared := (stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore })) _ = _
  rw [hBody']
  rfl

end FunDef

namespace Stmt

/-- Canonical caller continuation after one internal function body returns. -/
def finishCall (targets : List Functions.Name)
    (ctx : Functions.Source.Ctx) (stateAfterArgs : State)
    (callResult : Functions.InteractionSemantics.CallResult) :
    Open (Outcome × Functions.Source.Ctx) :=
  match callResult with
  | .returned stateAfterCall returnValues => do
      let returnStore ←
        (Functions.Source.Store.assignMany targets returnValues
          (stateModel.vars stateAfterArgs)).elim
            (throw .InvalidInstruction) pure
      let returnedSource := stateModel.source stateAfterCall
      pure
        (Functions.Source.Effectful.Outcome.regular
          (stateModel.withSource stateAfterCall
            { shared := returnedSource.shared, vars := returnStore }),
          ctx)
  | .halted kind haltedState =>
      pure (Functions.Source.Effectful.Outcome.halt kind haltedState, ctx)

/-- A successful regular call continuation supplies its canonical return
assignment rather than leaving it as generated evidence. -/
theorem successful_finishCall_returned
    (targets : List Functions.Name) (ctx : Functions.Source.Ctx)
    (stateAfterArgs sourceReturned : State) (returnValues : List Word)
    (hSuccess :
      Simulation.Interaction.Successful
        (finishCall targets ctx stateAfterArgs
          (.returned sourceReturned returnValues))) :
    ∃ returnStore,
      Functions.Source.Store.assignMany targets returnValues
          (stateModel.vars stateAfterArgs) =
        some returnStore := by
  cases hAssign : Functions.Source.Store.assignMany targets returnValues
      (stateModel.vars stateAfterArgs) with
  | none =>
      have hPrefix := Simulation.Interaction.Successful.bind_left hSuccess
      simp [finishCall, hAssign] at hPrefix
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hPrefix)
  | some returnStore => exact ⟨returnStore, rfl⟩

def openRunForLoop (program : Functions.Program)
    (loopCtx : Functions.Source.Ctx) (cond : Functions.Expr 1)
    (postBase : Functions.Source.Ctx) (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx) (body : Functions.Block)
    (fuel : Nat) (state : State) : Open Outcome :=
  Functions.Source.Canonical.Stmt.runForLoop
    stateModel primitiveSemantics program loopCtx cond
    postBase post bodyBase body fuel state

def openRun (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (state : State) :
    Open (Outcome × Functions.Source.Ctx) :=
  Functions.Source.Canonical.Stmt.run
    stateModel primitiveSemantics program ctx fuel stmt state

/-- One positive-fuel recursive loop iteration, exposed from the canonical
Functions semantics without duplicating its control interpreter. -/
theorem openRunForLoop_succ
    (program : Functions.Program) (loopCtx : Functions.Source.Ctx)
    (cond : Functions.Expr 1) (postBase : Functions.Source.Ctx)
    (post : Functions.Block) (bodyBase : Functions.Source.Ctx)
    (body : Functions.Block) (fuel : Nat) (state : State) :
    openRunForLoop program loopCtx cond postBase post bodyBase body
        (fuel + 1) state =
      Simulation.Interaction.bind (Expr.openEvalCondition cond state)
        (fun result =>
          if result.2 then
            Simulation.Interaction.bind
              (Block.openRunScoped program bodyBase body fuel result.1)
              (fun bodyOutcome =>
                match bodyOutcome.mode with
                | .brk =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        bodyOutcome.state)
                | .regular | .cont =>
                    Simulation.Interaction.bind
                      (Block.openRunScoped program postBase post fuel
                        bodyOutcome.state)
                      (fun postOutcome =>
                        match postOutcome.mode with
                        | .regular =>
                            openRunForLoop program loopCtx cond postBase post
                              bodyBase body fuel postOutcome.state
                        | .brk | .cont =>
                            Simulation.Interaction.error .InvalidInstruction
                        | .leave | .halt _ =>
                            Simulation.Interaction.pure postOutcome)
                | .leave | .halt _ =>
                    Simulation.Interaction.pure bodyOutcome)
          else
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.regular
                (result.1.restrictTo loopCtx.scope))) := by
  unfold openRunForLoop Functions.Source.Canonical.Stmt.runForLoop
  simp only [Functions.Source.Effectful.Control.Stmt.runForLoop]
  rfl

/-- The compiler's constant-true loop condition enters the body on every
positive target-fuel iteration. The source-level loop condition is implemented
by the guarded body and remains outside this semantic equation. -/
theorem openRunForLoop_true_succ
    (program : Functions.Program) (loopCtx : Functions.Source.Ctx)
    (postBase : Functions.Source.Ctx) (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx) (body : Functions.Block)
    (fuel : Nat) (state : State) :
    openRunForLoop program loopCtx
        (.lit (EvmYul.UInt256.ofNat 1)) postBase post bodyBase body
        (fuel + 1) state =
      Simulation.Interaction.bind
        (Block.openRunScoped program bodyBase body fuel state)
        (fun bodyOutcome =>
          match bodyOutcome.mode with
          | .brk =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  bodyOutcome.state)
          | .regular | .cont =>
              Simulation.Interaction.bind
                (Block.openRunScoped program postBase post fuel
                  bodyOutcome.state)
                (fun postOutcome =>
                  match postOutcome.mode with
                  | .regular =>
                      openRunForLoop program loopCtx
                        (.lit (EvmYul.UInt256.ofNat 1)) postBase post
                        bodyBase body fuel postOutcome.state
                  | .brk | .cont =>
                      Simulation.Interaction.error .InvalidInstruction
                  | .leave | .halt _ =>
                      Simulation.Interaction.pure postOutcome)
          | .leave | .halt _ =>
              Simulation.Interaction.pure bodyOutcome) := by
  rw [openRunForLoop_succ]
  have hOne :
      (EvmYul.UInt256.ofNat 1 != EvmYul.UInt256.ofNat 0) = true := by
    decide
  have hCondition :
      Expr.openEvalCondition (.lit (EvmYul.UInt256.ofNat 1)) state =
        Simulation.Interaction.pure (state, true) := by
    unfold Expr.openEvalCondition
      Locals.InteractionSemantics.Expr.openEvalCondition
      Locals.Source.Effectful.Expr.Control.evalCondition
      Locals.Source.Effectful.Expr.Control.evalOne
      Locals.Source.Effectful.Expr.Control.eval
    change
      Simulation.Interaction.pure
          (state,
            EvmYul.UInt256.ofNat 1 != EvmYul.UInt256.ofNat 0) =
        Simulation.Interaction.pure (state, true)
    rw [hOne]
  rw [hCondition]
  rfl

/-- The canonical positive-fuel `for` wrapper exposes initialization and its
recursive loop kernel. -/
theorem openRun_for
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (init : Functions.Block) (cond : Functions.Expr 1)
    (post body : Functions.Block) (state : State) :
    openRun program ctx (fuel + 1) (.for_ init cond post body) state =
      Simulation.Interaction.bind
        (Block.openRun program ctx.withoutLoopControl fuel init state)
        (fun initResult =>
          match initResult.1.mode with
          | .regular =>
              Simulation.Interaction.bind
                (openRunForLoop program initResult.2 cond
                  initResult.2.withoutLoopControl post
                  (initResult.2.withLoopControl
                    initResult.2.scope initResult.2.scope)
                  body fuel initResult.1.state)
                (fun loopOutcome =>
                  match loopOutcome.mode with
                  | .regular =>
                      Simulation.Interaction.pure
                        (Functions.Source.Effectful.Outcome.regular
                          (loopOutcome.state.restrictTo ctx.scope), ctx)
                  | .brk | .cont =>
                      Simulation.Interaction.error .InvalidInstruction
                  | .leave | .halt _ =>
                      Simulation.Interaction.pure (loopOutcome, ctx))
          | .brk | .cont =>
              Simulation.Interaction.error .InvalidInstruction
          | .leave | .halt _ =>
              Simulation.Interaction.pure (initResult.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  rfl

/-- The exact wrapper emitted by the Yul compiler: an empty initializer and a
constant-true kernel. Loop-control scopes are installed only for the body. -/
theorem openRun_for_empty_true
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (post body : Functions.Block) (state : State) :
    openRun program ctx (fuel + 2)
        (.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
          post body) state =
      Simulation.Interaction.bind
        (openRunForLoop program ctx.withoutLoopControl
          (.lit (EvmYul.UInt256.ofNat 1)) ctx.withoutLoopControl post
          (ctx.withLoopControl ctx.scope ctx.scope) body
          (fuel + 1) state)
        (fun loopOutcome =>
          match loopOutcome.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (loopOutcome.state.restrictTo ctx.scope), ctx)
          | .brk | .cont =>
              Simulation.Interaction.error .InvalidInstruction
          | .leave | .halt _ =>
              Simulation.Interaction.pure (loopOutcome, ctx)) := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega, openRun_for,
    Block.openRun_nil]
  rfl

theorem openRun_expr
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (expr : Functions.Expr 0) (state : State) :
    openRun program ctx fuel (.expr expr) state =
      Simulation.Interaction.bind (Expr.openEval expr state)
        (fun result =>
          pure (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  simp [openRun, Expr.openEval, Functions.Source.Canonical.Stmt.run,
    Functions.Source.Effectful.Control.Stmt.run,
    Locals.InteractionSemantics.Expr.openEval, stateModel,
    primitiveSemantics]
  change
    Simulation.Interaction.bind
        (Expr.openEval expr state)
        (fun result =>
          pure (Functions.Source.Effectful.Outcome.regular result.1, ctx)) =
      Simulation.Interaction.bind
        (Expr.openEval expr state)
        (fun result =>
          pure (Functions.Source.Effectful.Outcome.regular result.1, ctx))
  rfl

theorem openRun_brk
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) {scope : List Functions.Name}
    (hScope : ctx.breakScope? = some scope) :
    openRun program ctx fuel .brk state =
      pure
        (Functions.Source.Effectful.Outcome.brk
          (state.restrictTo scope), ctx) := by
  simp [openRun, Functions.Source.Canonical.Stmt.run,
    Functions.Source.Effectful.Control.Stmt.run, hScope, stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]

theorem openRun_cont
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) {scope : List Functions.Name}
    (hScope : ctx.continueScope? = some scope) :
    openRun program ctx fuel .cont state =
      pure
        (Functions.Source.Effectful.Outcome.cont
          (state.restrictTo scope), ctx) := by
  simp [openRun, Functions.Source.Canonical.Stmt.run,
    Functions.Source.Effectful.Control.Stmt.run, hScope, stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]

theorem openRun_leave
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) {scope : List Functions.Name}
    (hScope : ctx.leaveScope? = some scope) :
    openRun program ctx fuel .leave state =
      pure
        (Functions.Source.Effectful.Outcome.leave
          (state.restrictTo scope), ctx) := by
  simp [openRun, Functions.Source.Canonical.Stmt.run,
    Functions.Source.Effectful.Control.Stmt.run, hScope, stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]

theorem openRun_let
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (name : Functions.Name) (expr : Functions.Expr 1)
    (state : State) :
    openRun program ctx fuel (.let_ name expr) state =
      Simulation.Interaction.bind (Expr.openEval expr state)
        (fun result =>
          match result.2 with
          | [value] =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (stateModel.insert result.1 name value),
                  { ctx with scope := name :: ctx.scope })
          | _ => throw .InvalidInstruction) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  change
    Simulation.Interaction.bind
        (Locals.InteractionSemantics.Expr.openEvalOne expr state)
        (fun result =>
          pure
            (Functions.Source.Effectful.Outcome.regular
              (stateModel.insert result.1 name result.2),
              { ctx with scope := name :: ctx.scope })) = _
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial (Expr.openEval expr state))
  intro result _hResult
  cases result.2 with
  | nil => rfl
  | cons value rest =>
      cases rest <;> rfl

theorem openRun_let_lit
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (name : Functions.Name) (value : Word)
    (state : State) :
    openRun program ctx fuel (.let_ name (.lit value)) state =
      pure
        (Functions.Source.Effectful.Outcome.regular
          (state.insert name value),
          { ctx with scope := name :: ctx.scope }) := by
  rw [openRun_let]
  simp [Expr.openEval, Locals.InteractionSemantics.Expr.openEval,
    Locals.Source.Effectful.Expr.Control.eval,
    Locals.Source.Effectful.Expr.eval, stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel]
  rfl

theorem openRun_assign
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (name : Functions.Name) (expr : Functions.Expr 1)
    (state : State) (hContains : state.vars.contains name = true) :
    openRun program ctx fuel (.assign name expr) state =
      Simulation.Interaction.bind (Expr.openEval expr state)
        (fun result =>
          match result.2 with
          | [value] =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (stateModel.withVars result.1
                    (Locals.Source.Store.insert result.1.vars name value)),
                  ctx)
          | _ => throw .InvalidInstruction) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  have hContains' :
      (stateModel.vars state).contains name = true := by
    simpa [stateModel, Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Locals.Source.Effectful.StateModel.vars] using hContains
  simp only [hContains', if_pos]
  change
    Simulation.Interaction.bind
        (Locals.InteractionSemantics.Expr.openEvalOne expr state)
        (fun result =>
          pure
            (Functions.Source.Effectful.Outcome.regular
              (stateModel.withVars result.1
                (Locals.Source.Store.insert result.1.vars name result.2)),
              ctx)) = _
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial (Expr.openEval expr state))
  intro result _hResult
  cases result.2 with
  | nil => rfl
  | cons value rest =>
      cases rest <;> rfl

/-- Successful canonical call execution has positive caller meta-fuel. -/
theorem successful_openRun_call_fuel_pos
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {targets : List Functions.Name}
    {functionName : Functions.Name} {args : List (Functions.Expr 1)}
    {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx fuel (.call targets functionName args) state)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      unfold openRun Functions.Source.Canonical.Stmt.run at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.OutOfFuel : EVMException) hSuccess)
  | succ fuel => omega

/-- Successful canonical `for` execution has positive statement meta-fuel. -/
theorem successful_openRun_for_fuel_pos
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block} {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx fuel (.for_ init cond post body) state)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      unfold openRun Functions.Source.Canonical.Stmt.run at hSuccess
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
      exact False.elim
        (Simulation.Interaction.Successful.error_false
          (.OutOfFuel : EVMException) hSuccess)
  | succ fuel => omega

/-- A successful positive-fuel `for` statement exposes its initializer run. -/
theorem successful_openRun_for_init
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block} {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx (fuel + 1) (.for_ init cond post body) state)) :
    Simulation.Interaction.Successful
      (Block.openRun program ctx.withoutLoopControl fuel init state) := by
  unfold openRun Functions.Source.Canonical.Stmt.run at hSuccess
  simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
  unfold Block.openRun Functions.Source.Canonical.Block.runOpen
  exact Simulation.Interaction.Successful.bind_left hSuccess

/-- A lexical block restricts its state only after regular body completion. -/
theorem openRun_block
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (body : Functions.Block) (state : State) :
    openRun program ctx fuel (.block body) state =
      Simulation.Interaction.bind
        (Block.openRun program ctx fuel body state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (stateModel.restrictTo ctx.scope result.1.state), ctx)
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) := by
  unfold openRun Block.openRun Functions.Source.Canonical.Stmt.run
    Functions.Source.Canonical.Block.runOpen
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Functions.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Functions.Source.Effectful.Control.Block.runOpen
            stateModel primitiveSemantics program ctx fuel body state)
          (fun result =>
            match result.1.mode with
            | .regular =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular
                    (stateModel.restrictTo ctx.scope result.1.state))
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure result.1))
        (fun outcome => Simulation.Interaction.pure (outcome, ctx)) = _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.Source.Effectful.Control.Block.runOpen
        stateModel primitiveSemantics program ctx fuel body state))
  intro result _
  cases hMode : result.1.mode <;> rfl

theorem openRun_block_eq_scoped_pair
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (body : Functions.Block) (state : State) :
    openRun program ctx fuel (.block body) state =
      Simulation.Interaction.bind
        (Block.openRunScoped program ctx body fuel state)
        (fun outcome => Simulation.Interaction.pure (outcome, ctx)) := by
  rw [openRun_block, Block.openRunScoped_eq_bind,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Block.openRun program ctx fuel body state))
  intro result _
  cases hMode : result.1.mode <;> rfl

/-- A positive-fuel lexical singleton break returns the handler-restricted
break outcome. This is the exact synthetic body emitted by the Yul loop guard. -/
theorem openRun_block_brk
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) {scope : List Functions.Name}
    (hScope : ctx.breakScope? = some scope) :
    openRun program ctx (fuel + 1) (.block { stmts := [.brk] }) state =
      Simulation.Interaction.pure
        (Functions.Source.Effectful.Outcome.brk
          (state.restrictTo scope), ctx) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp [Functions.Source.Effectful.Control.Stmt.run,
    Functions.Source.Effectful.Control.Block.runScoped,
    Functions.Source.Effectful.Control.Block.runOpen, hScope, stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]
  rfl

/-- A positive-fuel conditional exposes condition evaluation and one branch. -/
theorem openRun_if
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (cond : Functions.Expr 1) (body : Functions.Block)
    (state : State) :
    openRun program ctx (fuel + 1) (.if_ cond body) state =
      Simulation.Interaction.bind
        (Expr.openEvalCondition cond state)
        (fun result =>
          if result.2 then
            openRun program ctx fuel (.block body) result.1
          else
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Expr.openEvalCondition
    Locals.InteractionSemantics.Expr.openEvalCondition
  rfl

/-- A positive-fuel switch exposes one scrutinee and its selected branch. -/
theorem openRun_switch
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block) (state : State) :
    openRun program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) state =
      Simulation.Interaction.bind
        (Expr.openEvalOne scrutinee state)
        (fun result =>
          match Functions.Source.Switch.select
              result.2 cases defaultBody with
          | some body => openRun program ctx fuel (.block body) result.1
          | none =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Expr.openEvalOne
    Locals.InteractionSemantics.Expr.openEvalOne stateModel primitiveSemantics
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.Source.Effectful.Expr.Control.evalOne
        Locals.InteractionSemantics.stateModel
        Locals.InteractionSemantics.primitiveSemantics scrutinee state))
  intro result _
  cases Functions.Source.Switch.select result.2 cases defaultBody <;> rfl

/-- A positive-fuel internal call exposes arguments, body execution, and writeback. -/
theorem openRun_call
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (targets : List Functions.Name)
    (functionName : Functions.Name) (args : List (Functions.Expr 1))
    (state : State) :
    openRun program ctx (fuel + 1) (.call targets functionName args) state =
      (do
        if targets.Nodup then
          let (stateAfterArgs, argValues) ←
            Functions.Source.Effectful.ArgList.Control.eval
              stateModel primitiveSemantics args state
          let fn ←
            (Functions.Source.FunList.find? functionName program.functions).elim
              (throw .InvalidInstruction) pure
          let callResult ←
            Functions.Source.Effectful.Control.FunDef.runBody
              stateModel primitiveSemantics program fn argValues fuel
                stateAfterArgs
          finishCall targets ctx stateAfterArgs callResult
        else
          throw .InvalidInstruction) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  by_cases hTargets : targets.Nodup
  · simp only [if_pos hTargets]
    apply Simulation.Interaction.AllDone.bind_congr
      (Simulation.Interaction.AllDone.trivial
        (Functions.Source.Effectful.ArgList.Control.eval
          stateModel primitiveSemantics args state))
    intro result _
    rcases result with ⟨stateAfterArgs, argValues⟩
    cases hFind : Functions.Source.FunList.find?
        functionName program.functions with
    | none =>
        simp only [hFind]
        change Simulation.Interaction.bind
            (Simulation.Interaction.error (Error := EVMException)
              (Result := Functions.FunDef) .InvalidInstruction) _ =
          Simulation.Interaction.bind
            (Simulation.Interaction.error (Error := EVMException)
              (Result := Functions.FunDef) .InvalidInstruction) _
        rfl
    | some fn =>
        simp only [hFind]
        change Simulation.Interaction.bind
            (Simulation.Interaction.pure (Error := EVMException) fn) _ =
          Simulation.Interaction.bind
            (Simulation.Interaction.pure (Error := EVMException) fn) _
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Simulation.Interaction.pure (Error := EVMException) fn))
        intro fn _
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Functions.Source.Effectful.Control.FunDef.runBody
              stateModel primitiveSemantics program fn argValues fuel
                stateAfterArgs))
        intro callResult _
        cases callResult with
        | returned stateAfterCall returnValues =>
            cases hAssign : Functions.Source.Store.assignMany
                targets returnValues (stateModel.vars stateAfterArgs) with
            | none =>
                simp [finishCall, hAssign, Simulation.Interaction.error,
                  Simulation.Interaction.pure, Simulation.Interaction.bind]
            | some returnStore =>
                simp [finishCall, hAssign, Simulation.Interaction.error,
                  Simulation.Interaction.pure, Simulation.Interaction.bind]
        | halted kind haltedState =>
            simp [finishCall]
  · simp only [if_neg hTargets]

/-- Successful canonical call execution exposes the real source function and
successful `runBody` continuation on every open-world argument branch. -/
theorem successful_openRun_call_parts
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (targets : List Functions.Name)
    (functionName : Functions.Name) (args : List (Functions.Expr 1))
    (state : State) (hTargets : targets.Nodup)
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx (fuel + 1)
          (.call targets functionName args) state)) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => False
        | .ok result =>
            ∃ fn,
              Functions.Source.FunList.find? functionName program.functions =
                  some fn ∧
                Simulation.Interaction.Successful
                  (Functions.InteractionSemantics.FunDef.openRunBody
                    program fn result.2 fuel result.1))
      (Functions.InteractionSemantics.ArgList.openEval args state) := by
  rw [openRun_call] at hSuccess
  simp only [hTargets, if_pos] at hSuccess
  have hArgs := Simulation.Interaction.Successful.bind_inv hSuccess
  apply Simulation.Interaction.AllDone.mono hArgs
  intro outcome hOutcome
  cases outcome with
  | error _ => exact hOutcome
  | ok result =>
      rcases result with ⟨stateAfterArgs, argValues⟩
      cases hFind :
          Functions.Source.FunList.find? functionName program.functions with
      | none =>
          have hLookup := Simulation.Interaction.Successful.bind_left hOutcome
          simp only [hFind, Option.elim_none] at hLookup
          exact False.elim
            (Simulation.Interaction.Successful.error_false _ hLookup)
      | some fn =>
          refine ⟨fn, rfl, ?_⟩
          simp only [hFind, Option.elim_some,
            Simulation.Interaction.bind_done_ok] at hOutcome
          exact Simulation.Interaction.Successful.bind_left hOutcome

/-- Successful call execution exposes the exact successful caller
continuation after every open-world callee result. -/
theorem successful_openRun_call_continuations
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (targets : List Functions.Name)
    (functionName : Functions.Name) (args : List (Functions.Expr 1))
    (state : State) (hTargets : targets.Nodup)
    (hSuccess :
      Simulation.Interaction.Successful
        (openRun program ctx (fuel + 1)
          (.call targets functionName args) state)) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => False
        | .ok result =>
            ∃ fn,
              Functions.Source.FunList.find? functionName program.functions =
                  some fn ∧
                Simulation.Interaction.AllDone
                  (fun callDone =>
                    match callDone with
                    | .error _ => False
                    | .ok callResult =>
                        Simulation.Interaction.Successful
                          (finishCall targets ctx result.1 callResult))
                  (Functions.InteractionSemantics.FunDef.openRunBody
                    program fn result.2 fuel result.1))
      (Functions.InteractionSemantics.ArgList.openEval args state) := by
  rw [openRun_call] at hSuccess
  simp only [hTargets, if_pos] at hSuccess
  have hArgs := Simulation.Interaction.Successful.bind_inv hSuccess
  apply Simulation.Interaction.AllDone.mono hArgs
  intro outcome hOutcome
  cases outcome with
  | error _ => exact hOutcome
  | ok result =>
      rcases result with ⟨stateAfterArgs, argValues⟩
      cases hFind : Functions.Source.FunList.find?
          functionName program.functions with
      | none =>
          have hLookup := Simulation.Interaction.Successful.bind_left hOutcome
          simp only [hFind, Option.elim_none] at hLookup
          exact False.elim
            (Simulation.Interaction.Successful.error_false _ hLookup)
      | some fn =>
          refine ⟨fn, rfl, ?_⟩
          simp only [hFind, Option.elim_some,
            Simulation.Interaction.bind_done_ok] at hOutcome
          have hFn := Simulation.Interaction.Successful.bind_inv hOutcome
          cases hFn with
          | done hFnSuccess =>
              change Simulation.Interaction.AllDone
                (fun callDone =>
                  match callDone with
                  | .error _ => False
                  | .ok callResult =>
                      Simulation.Interaction.Successful
                        (finishCall targets ctx stateAfterArgs callResult))
                (Functions.Source.Effectful.Control.FunDef.runBody
                  stateModel primitiveSemantics program fn argValues fuel
                  stateAfterArgs)
              apply Simulation.Interaction.AllDone.mono
                (Simulation.Interaction.Successful.bind_inv hFnSuccess)
              intro callDone hDone
              cases callDone <;> exact hDone

end Stmt

mutual
  def Block.OpenSupported : Functions.Block → Prop
    | ⟨stmts⟩ => StmtList.OpenSupported stmts

  def Stmt.OpenSupported : Functions.Stmt → Prop
    | .expr expr => Locals.InteractionSemantics.Expr.OpenSupported expr
    | .let_ _name value =>
        Locals.InteractionSemantics.Expr.OpenSupported value
    | .assign _name value =>
        Locals.InteractionSemantics.Expr.OpenSupported value
    | .block body => Block.OpenSupported body
    | .if_ cond body =>
        Locals.InteractionSemantics.Expr.OpenSupported cond ∧
          Block.OpenSupported body
    | .switch scrutinee cases defaultBody =>
        Locals.InteractionSemantics.Expr.OpenSupported scrutinee ∧
          CaseList.OpenSupported cases ∧ Default.OpenSupported defaultBody
    | .for_ init cond post body =>
        Block.OpenSupported init ∧
          Locals.InteractionSemantics.Expr.OpenSupported cond ∧
          Block.OpenSupported post ∧ Block.OpenSupported body
    | .brk | .cont | .leave | .terminal _kind => True
    | .call _targets _functionName args => ArgList.OpenSupported args
    | .terminalArgs _kind args =>
        Locals.InteractionSemantics.ExprSeq.OpenSupported args

  def StmtList.OpenSupported : List Functions.Stmt → Prop
    | [] => True
    | stmt :: rest =>
        Stmt.OpenSupported stmt ∧ StmtList.OpenSupported rest

  def CaseList.OpenSupported : List (Word × Functions.Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.OpenSupported body ∧ CaseList.OpenSupported rest

  def Default.OpenSupported : Option Functions.Block → Prop
    | none => True
    | some body => Block.OpenSupported body
end

namespace Program

def openRunState (fuel : Nat) (program : Functions.Program)
    (state : State) : Open Outcome :=
  Functions.Source.Canonical.Program.runState
    stateModel primitiveSemantics fuel program state

/-- Successful whole-program execution exposes a successful canonical open
main block before top-level lexical restriction. -/
theorem successful_openRunState_open
    {fuel : Nat} {program : Functions.Program} {state : State}
    (hSuccess :
      Simulation.Interaction.Successful
        (openRunState fuel program state)) :
    Simulation.Interaction.Successful
      (Block.openRun program Functions.Source.Ctx.initial fuel
        program.body state) := by
  unfold openRunState Functions.Source.Canonical.Program.runState
    Functions.Source.Effectful.Control.Program.runState at hSuccess
  unfold Functions.Source.Effectful.Control.Block.runScoped at hSuccess
  exact Simulation.Interaction.Successful.bind_left hSuccess

def OpenSupported (program : Functions.Program) : Prop :=
  (∀ fn, fn ∈ program.functions → Block.OpenSupported fn.body) ∧
    Block.OpenSupported program.body

end Program

namespace Abrupt

def NonregularResult :
    Except EVMException (Outcome × Functions.Source.Ctx) → Prop
  | .error _ => True
  | .ok result => result.1.mode ≠ .regular

theorem stmt_allDone_of_alwaysExits
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (state : State)
    (hExit : stmt.alwaysExits = true) :
    Simulation.Interaction.AllDone NonregularResult
      (Stmt.openRun program ctx fuel stmt state) := by
  cases stmt with
  | expr _ => simp [Functions.Stmt.alwaysExits] at hExit
  | let_ _ _ => simp [Functions.Stmt.alwaysExits] at hExit
  | assign _ _ => simp [Functions.Stmt.alwaysExits] at hExit
  | block _ => simp [Functions.Stmt.alwaysExits] at hExit
  | if_ _ _ => simp [Functions.Stmt.alwaysExits] at hExit
  | switch _ _ _ => simp [Functions.Stmt.alwaysExits] at hExit
  | for_ _ _ _ _ => simp [Functions.Stmt.alwaysExits] at hExit
  | call _ _ _ => simp [Functions.Stmt.alwaysExits] at hExit
  | brk =>
      cases hScope : ctx.breakScope? with
      | none =>
          simp [Stmt.openRun, Functions.Source.Canonical.Stmt.run,
            Functions.Source.Effectful.Control.Stmt.run, hScope]
          apply Simulation.Interaction.AllDone.done
          trivial
      | some scope =>
          rw [Stmt.openRun_brk program ctx fuel state hScope]
          exact .done (by simp [NonregularResult])
  | cont =>
      cases hScope : ctx.continueScope? with
      | none =>
          simp [Stmt.openRun, Functions.Source.Canonical.Stmt.run,
            Functions.Source.Effectful.Control.Stmt.run, hScope]
          apply Simulation.Interaction.AllDone.done
          trivial
      | some scope =>
          rw [Stmt.openRun_cont program ctx fuel state hScope]
          exact .done (by simp [NonregularResult])
  | leave =>
      cases hScope : ctx.leaveScope? with
      | none =>
          simp [Stmt.openRun, Functions.Source.Canonical.Stmt.run,
            Functions.Source.Effectful.Control.Stmt.run, hScope]
          apply Simulation.Interaction.AllDone.done
          trivial
      | some scope =>
          rw [Stmt.openRun_leave program ctx fuel state hScope]
          exact .done (by simp [NonregularResult])
  | terminal kind =>
      unfold Stmt.openRun Functions.Source.Canonical.Stmt.run
        Functions.Source.Effectful.Control.Stmt.run
      apply Simulation.Interaction.AllDone.bind
        (Simulation.Interaction.AllDone.trivial
          (primitiveSemantics.terminal kind state []))
      · intro _error _hTrivial
        trivial
      · intro final _hTrivial
        exact .done (by simp [NonregularResult])
  | terminalArgs kind args =>
      unfold Stmt.openRun Functions.Source.Canonical.Stmt.run
        Functions.Source.Effectful.Control.Stmt.run
      apply Simulation.Interaction.AllDone.bind
        (Simulation.Interaction.AllDone.trivial
          (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
            stateModel primitiveSemantics args state))
      · intro _error _hTrivial
        trivial
      · intro result _hTrivial
        apply Simulation.Interaction.AllDone.bind
          (Simulation.Interaction.AllDone.trivial
            (primitiveSemantics.terminal kind result.1 result.2))
        · intro _error _hTrivial
          trivial
        · intro final _hTrivial
          exact .done (by simp [NonregularResult])

theorem block_allDone_of_hasDirectExit
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (block : Functions.Block) (state : State)
    (hExit : Functions.StmtList.hasDirectExit block.stmts = true) :
    Simulation.Interaction.AllDone NonregularResult
      (Block.openRun program ctx fuel block state) := by
  rcases block with ⟨stmts⟩
  induction stmts generalizing ctx fuel state with
  | nil =>
      simp [Functions.StmtList.hasDirectExit] at hExit
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [Block.openRun, Functions.Source.Canonical.Block.runOpen,
            Functions.Source.Effectful.Control.Block.runOpen]
          apply Simulation.Interaction.AllDone.done
          trivial
      | succ fuel =>
          unfold Block.openRun Functions.Source.Canonical.Block.runOpen
            Functions.Source.Effectful.Control.Block.runOpen
          by_cases hHead : stmt.alwaysExits = true
          · apply Simulation.Interaction.AllDone.bind
              (stmt_allDone_of_alwaysExits program ctx fuel stmt state hHead)
            · intro _error _hTrivial
              trivial
            · intro result hNonregular
              rcases result with ⟨⟨resultState, mode⟩, resultCtx⟩
              cases mode with
              | regular => exact False.elim (hNonregular rfl)
              | brk | cont | leave | halt _ =>
                  exact .done (by simp [NonregularResult])
          · have hTail : Functions.StmtList.hasDirectExit rest = true := by
              have hHeadFalse : stmt.alwaysExits = false :=
                Bool.eq_false_of_not_eq_true hHead
              unfold Functions.StmtList.hasDirectExit at hExit
              rw [hHeadFalse] at hExit
              simpa using hExit
            apply Simulation.Interaction.AllDone.bind
              (Simulation.Interaction.AllDone.trivial
                (Stmt.openRun program ctx fuel stmt state))
            · intro _error _hTrivial
              trivial
            · intro result _hTrivial
              rcases result with ⟨⟨resultState, mode⟩, resultCtx⟩
              cases mode with
              | regular =>
                  simpa [Block.openRun] using
                    ih resultCtx fuel resultState hTail
              | brk | cont | leave | halt _ =>
                  exact .done (by simp [NonregularResult])

end Abrupt

end InteractionSemantics
end Functions
end EvmCompiler
