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
          (.InvalidInstruction : EVMException) hSuccess)
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

end Block

namespace FunDef

def openRunBody (program : Functions.Program) (fn : Functions.FunDef)
    (args : List Word) (fuel : Nat) (state : State) : Open CallResult :=
  Functions.Source.Canonical.FunDef.runBody
    stateModel primitiveSemantics program fn args fuel state

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

def OpenSupported (program : Functions.Program) : Prop :=
  (∀ fn, fn ∈ program.functions → Block.OpenSupported fn.body) ∧
    Block.OpenSupported program.body

end Program

end InteractionSemantics
end Functions
end EvmCompiler
