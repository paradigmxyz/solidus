import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Functions.InteractionRefinement

/-!
Canonical Functions semantics with allocation memory safety enforced at the
primitive boundary. Control remains the shared parameterized Functions
interpreter; this module supplies only the primitive capability required by
the adjacent allocation pass.
-/

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSafeSemantics

abbrev Open (alpha : Type) := Simulation.Interaction EVMException alpha
abbrev State := Functions.InteractionSemantics.State
abbrev Outcome := Functions.Source.Effectful.Outcome State

noncomputable def openEval (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (state : State) (values : List Assembly.Word) :
    Open (State × List Assembly.Word) := by
  classical
  exact
    if AllocationInteractionPrimitive.PrimitiveSafe contract op state values then
      Locals.InteractionSemantics.Primitive.openEval op state values
    else
      throw .InvalidInstruction

noncomputable def openTerminal (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind) (state : State)
    (values : List Assembly.Word) : Open State := by
  classical
  exact
    if Simulation.MemorySafety.TerminalMemorySafe contract kind values then
      Locals.InteractionSemantics.Primitive.openTerminal kind state values
    else
      throw .InvalidInstruction

noncomputable def primitiveSemantics (contract : MemoryContract.Contract) :
    Functions.Source.Canonical.PrimitiveSemantics Open State where
  eval := openEval contract
  terminal := openTerminal contract

namespace Primitive

theorem safe_of_successful
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    {state : State} {values : List Assembly.Word}
    (hSuccess : Simulation.Interaction.Successful
      (openEval contract op state values)) :
    AllocationInteractionPrimitive.PrimitiveSafe contract op state values := by
  by_contra hUnsafe
  unfold openEval at hSuccess
  simp only [hUnsafe, ↓reduceIte] at hSuccess
  exact Simulation.Interaction.Successful.error_false _ hSuccess

theorem terminalSafe_of_successful
    {contract : MemoryContract.Contract} {kind : Assembly.HaltKind}
    {state : State} {values : List Assembly.Word}
    (hSuccess : Simulation.Interaction.Successful
      (openTerminal contract kind state values)) :
    Simulation.MemorySafety.TerminalMemorySafe contract kind values := by
  by_contra hUnsafe
  unfold openTerminal at hSuccess
  simp only [hUnsafe, ↓reduceIte] at hSuccess
  exact Simulation.Interaction.Successful.error_false _ hSuccess

theorem openEval_eq_ordinary
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    {state : State} {values : List Assembly.Word}
    (hSafe :
      AllocationInteractionPrimitive.PrimitiveSafe contract op state values) :
    openEval contract op state values =
      Locals.InteractionSemantics.Primitive.openEval op state values := by
  simp [openEval, hSafe]

theorem openTerminal_eq_ordinary
    {contract : MemoryContract.Contract} {kind : Assembly.HaltKind}
    {state : State} {values : List Assembly.Word}
    (hSafe :
      Simulation.MemorySafety.TerminalMemorySafe contract kind values) :
    openTerminal contract kind state values =
      Locals.InteractionSemantics.Primitive.openTerminal kind state values := by
  simp [openTerminal, hSafe]

theorem supportsOpen_of_successful
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    {state : State} {values : List Assembly.Word}
    (hSuccess : Simulation.Interaction.Successful
      (openEval contract op state values)) :
    Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
  have hSafe := safe_of_successful hSuccess
  have hOrdinary : Simulation.Interaction.Successful
      (Locals.InteractionSemantics.Primitive.openEval op state values) := by
    simpa [openEval_eq_ordinary hSafe] using hSuccess
  by_contra hUnsupported
  unfold Locals.InteractionSemantics.Primitive.openEval at hOrdinary
  by_cases hLength :
      values.length = Expressions.Structured.BasicOp.inputs op
  · simp only [hLength, hUnsupported, ↓reduceIte] at hOrdinary
    exact Simulation.Interaction.Successful.error_false _ hOrdinary
  · simp only [hLength, ↓reduceIte] at hOrdinary
    exact Simulation.Interaction.Successful.error_false _ hOrdinary

theorem openEval_vars_eq
    (contract : MemoryContract.Contract) (op : Structured.BasicOp)
    (state : State) (values : List Assembly.Word) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval contract op state values) := by
  classical
  by_cases hSafe :
      AllocationInteractionPrimitive.PrimitiveSafe contract op state values
  · rw [openEval_eq_ordinary hSafe]
    exact Locals.InteractionSemantics.Primitive.openEval_vars_eq
      op state values
  · unfold openEval
    simp only [hSafe, ↓reduceIte]
    exact .done True.intro

end Primitive

/-- The guarded primitive capability is an exact successful refinement of the
ordinary open capability. In particular, safe GAS/MSIZE/CALL/CREATE/LOG effects
are delegated unchanged rather than reinterpreted. -/
theorem primitive_successRefines_ordinary
    (contract : MemoryContract.Contract) :
    Functions.InteractionRefinement.SuccessRefines
      (primitiveSemantics contract)
      Functions.InteractionSemantics.primitiveSemantics := by
  constructor
  · intro op state values hSuccessful
    exact Primitive.openEval_eq_ordinary
      (Primitive.safe_of_successful hSuccessful)
  · intro kind state values hSuccessful
    exact Primitive.openTerminal_eq_ordinary
      (Primitive.terminalSafe_of_successful hSuccessful)

namespace Expr

noncomputable def openEval {results : Nat}
    (contract : MemoryContract.Contract) (expr : Functions.Expr results)
    (state : State) : Open (State × List Assembly.Word) :=
  Locals.Source.Effectful.Expr.Control.eval
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) expr state

noncomputable def openEvalOne (contract : MemoryContract.Contract)
    (expr : Functions.Expr 1) (state : State) :
    Open (State × Assembly.Word) :=
  Locals.Source.Effectful.Expr.Control.evalOne
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) expr state

noncomputable def openEvalCondition (contract : MemoryContract.Contract)
    (expr : Functions.Expr 1) (state : State) : Open (State × Bool) :=
  Locals.Source.Effectful.Expr.Control.evalCondition
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) expr state

mutual
  theorem openEval_vars_eq {results : Nat}
      (contract : MemoryContract.Contract) (expr : Functions.Expr results)
      (state : State) :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result => result.1.vars = state.vars)
        (openEval contract expr state) := by
    cases expr with
    | lit value => exact .done rfl
    | var name =>
        cases hLookup : state.vars name with
        | none =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => Simulation.Interaction.pure (state, [value])
              | none => throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done True.intro
        | some value =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => Simulation.Interaction.pure (state, [value])
              | none => throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done rfl
    | code code => exact .done True.intro
    | prim op args =>
        unfold openEval Locals.Source.Effectful.Expr.Control.eval
        apply Simulation.Interaction.AllDone.bind
          (openEvalSeq_vars_eq contract args state)
        · intro _ _
          trivial
        · intro result hArgs
          rcases result with ⟨afterArgs, values⟩
          apply Simulation.Interaction.AllDone.mono
            (Primitive.openEval_vars_eq contract op afterArgs values)
          intro outcome hOutcome
          cases outcome with
          | error _ => trivial
          | ok result => exact hOutcome.trans hArgs

  theorem openEvalSeq_vars_eq {results : Nat}
      (contract : MemoryContract.Contract) (exprs : Locals.ExprSeq results)
      (state : State) :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result => result.1.vars = state.vars)
        (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
          Functions.InteractionSemantics.stateModel
          (primitiveSemantics contract) exprs state) := by
    cases exprs with
    | nil => exact .done rfl
    | cons head tail =>
        unfold Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        apply Simulation.Interaction.AllDone.bind
          (openEval_vars_eq contract head state)
        · intro _ _
          trivial
        · intro headResult hHead
          rcases headResult with ⟨afterHead, headValues⟩
          apply Simulation.Interaction.AllDone.bind
            (openEvalSeq_vars_eq contract tail afterHead)
          · intro _ _
            trivial
          · intro tailResult hTail
            rcases tailResult with ⟨afterTail, tailValues⟩
            exact .done (hTail.trans hHead)
end

theorem openEvalOne_vars_eq
    (contract : MemoryContract.Contract) (expr : Functions.Expr 1)
    (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEvalOne contract expr state) := by
  unfold openEvalOne Locals.Source.Effectful.Expr.Control.evalOne
  apply Simulation.Interaction.AllDone.bind
    (openEval_vars_eq contract expr state)
  · intro _err _hVars
    trivial
  · intro result hVars
    rcases result with ⟨after, values⟩
    cases values with
    | nil => exact .done True.intro
    | cons value rest =>
        cases rest with
        | nil => exact .done hVars
        | cons other tail => exact .done True.intro

theorem openEvalCondition_vars_eq
    (contract : MemoryContract.Contract) (expr : Functions.Expr 1)
    (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEvalCondition contract expr state) := by
  unfold openEvalCondition Locals.Source.Effectful.Expr.Control.evalCondition
  apply Simulation.Interaction.AllDone.bind
    (openEvalOne_vars_eq contract expr state)
  · intro _err _hVars
    trivial
  · intro result hVars
    exact .done hVars

end Expr

namespace ExprSeq

noncomputable def openEval {results : Nat}
    (contract : MemoryContract.Contract) (exprs : Locals.ExprSeq results)
    (state : State) : Open (State × List Assembly.Word) :=
  Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) exprs state

theorem openEval_vars_eq {results : Nat}
    (contract : MemoryContract.Contract) (exprs : Locals.ExprSeq results)
    (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval contract exprs state) :=
  Expr.openEvalSeq_vars_eq contract exprs state

end ExprSeq

namespace ArgList

noncomputable def openEval (contract : MemoryContract.Contract)
    (args : List (Functions.Expr 1)) (state : State) :
    Open (State × List Assembly.Word) :=
  Functions.Source.Canonical.ArgList.eval
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) args state

theorem openEval_vars_eq (contract : MemoryContract.Contract)
    (args : List (Functions.Expr 1)) (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval contract args state) := by
  induction args generalizing state with
  | nil => exact .done rfl
  | cons arg rest ih =>
      unfold openEval Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval
      apply Simulation.Interaction.AllDone.bind
        (Expr.openEvalOne_vars_eq contract arg state)
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

theorem openEval_eq_ordinary_of_successful
    (contract : MemoryContract.Contract)
    (args : List (Functions.Expr 1)) (state : State)
    (hSuccessful : Simulation.Interaction.Successful
      (openEval contract args state)) :
    openEval contract args state =
      Functions.InteractionSemantics.ArgList.openEval args state := by
  exact
    Functions.InteractionRefinement.ArgList.eval_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract) args state hSuccessful

end ArgList

namespace Block

noncomputable def openRun (contract : MemoryContract.Contract)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (block : Functions.Block) (state : State) :
    Open (Outcome × Functions.Source.Ctx) :=
  Functions.Source.Canonical.Block.runOpen
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) program ctx fuel block state

/-- Reservation/host safety for one concrete block execution. It quantifies
over every answer branch generated by that execution, not over unrelated
syntax or states. -/
def ExecutionSafe (contract : MemoryContract.Contract)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (block : Functions.Block) (state : State) : Prop :=
  Simulation.Interaction.Successful
    (openRun contract program ctx fuel block state)

noncomputable def openRunScoped (contract : MemoryContract.Contract)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (block : Functions.Block) (fuel : Nat) (state : State) : Open Outcome :=
  Functions.Source.Canonical.Block.runScoped
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) program ctx block fuel state

end Block

namespace FunDef

noncomputable def openRunBody (contract : MemoryContract.Contract)
    (program : Functions.Program) (fn : Functions.FunDef)
    (args : List Word) (fuel : Nat) (state : State) :
    Open Functions.InteractionSemantics.CallResult :=
  Functions.Source.Canonical.FunDef.runBody
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) program fn args fuel state

theorem openRunBody_eq_ordinary_of_successful
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (fn : Functions.FunDef) (args : List Word) (fuel : Nat)
    (state : State)
    (hSuccessful : Simulation.Interaction.Successful
      (openRunBody contract program fn args fuel state)) :
    openRunBody contract program fn args fuel state =
      Functions.InteractionSemantics.FunDef.openRunBody
        program fn args fuel state := by
  exact
    Functions.InteractionRefinement.FunDef.runBody_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract)
      program fn args fuel state hSuccessful

/-- A successful guarded function execution exposes its exact initialized
callee body one fuel level below the call wrapper. -/
theorem successful_openRunBody_parts
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (fn : Functions.FunDef) (args : List Word) (fuel : Nat) (state : State)
    (hSuccessful : Simulation.Interaction.Successful
      (openRunBody contract program fn args (fuel + 1) state)) :
    ∃ paramStore,
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore ∧
        Block.ExecutionSafe contract program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) fuel fn.body
          (Functions.InteractionSemantics.stateModel.withSource state
            { shared :=
                (Functions.InteractionSemantics.stateModel.source state).shared
              vars := Functions.Source.Store.initReturns
                fn.returns paramStore }) := by
  unfold openRunBody Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody at hSuccessful
  cases hParams : Functions.Source.Store.insertMany fn.params args
      Locals.Source.Store.empty with
  | none =>
      have hPrefix := Simulation.Interaction.Successful.bind_left hSuccessful
      simp only [hParams, Option.elim_none] at hPrefix
      exact False.elim
        (Simulation.Interaction.Successful.error_false _ hPrefix)
  | some paramStore =>
      refine ⟨paramStore, rfl, ?_⟩
      simp only [hParams, Option.elim_some,
        Simulation.Interaction.bind_done_ok] at hSuccessful
      exact Simulation.Interaction.Successful.bind_left hSuccessful

end FunDef

namespace Stmt

noncomputable def openRunForLoop (contract : MemoryContract.Contract)
    (program : Functions.Program) (loopCtx : Functions.Source.Ctx)
    (cond : Functions.Expr 1) (postCtx : Functions.Source.Ctx)
    (post : Functions.Block) (bodyCtx : Functions.Source.Ctx)
    (body : Functions.Block) (fuel : Nat) (state : State) : Open Outcome :=
  Functions.Source.Effectful.Control.Stmt.runForLoop
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) program loopCtx cond postCtx post bodyCtx
      body fuel state

noncomputable def openRun (contract : MemoryContract.Contract)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (state : State) :
    Open (Outcome × Functions.Source.Ctx) :=
  Functions.Source.Canonical.Stmt.run
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) program ctx fuel stmt state

/-- A positive-fuel guarded internal call exposes argument evaluation, the
selected function body, and the ordinary source writeback operation. -/
theorem openRun_call
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (targets : List Functions.Name) (functionName : Functions.Name)
    (args : List (Functions.Expr 1)) (state : State) :
    openRun contract program ctx (fuel + 1)
        (.call targets functionName args) state =
      (do
        if targets.Nodup then
          let (stateAfterArgs, argValues) <-
            ArgList.openEval contract args state
          let fn <-
            (Functions.Source.FunList.find? functionName program.functions).elim
              (throw .InvalidInstruction) pure
          let callResult <-
            FunDef.openRunBody contract program fn argValues fuel stateAfterArgs
          Functions.InteractionSemantics.Stmt.finishCall
            targets ctx stateAfterArgs callResult
        else
          throw .InvalidInstruction) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  by_cases hTargets : targets.Nodup
  · simp only [if_pos hTargets]
    apply Simulation.Interaction.AllDone.bind_congr
      (Simulation.Interaction.AllDone.trivial
        (ArgList.openEval contract args state))
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
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Simulation.Interaction.pure (Error := EVMException) fn))
        intro fn _
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (FunDef.openRunBody contract program fn argValues fuel
              stateAfterArgs))
        intro callResult _
        cases callResult with
        | returned stateAfterCall returnValues =>
            cases hAssign : Functions.Source.Store.assignMany
                targets returnValues
                  (Functions.InteractionSemantics.stateModel.vars
                    stateAfterArgs) <;>
              simp [Functions.InteractionSemantics.Stmt.finishCall, hAssign]
        | halted kind haltedState =>
            simp [Functions.InteractionSemantics.Stmt.finishCall]
  · simp only [if_neg hTargets]

/-- Successful guarded call execution exposes the selected guarded body and
the exact successful caller continuation on every open-world branch. -/
theorem successful_openRun_call_continuations
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (targets : List Functions.Name) (functionName : Functions.Name)
    (args : List (Functions.Expr 1)) (state : State)
    (hTargets : targets.Nodup)
    (hSuccess : Simulation.Interaction.Successful
      (openRun contract program ctx (fuel + 1)
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
                          (Functions.InteractionSemantics.Stmt.finishCall
                            targets ctx result.1 callResult))
                  (FunDef.openRunBody contract program fn result.2 fuel
                    result.1))
      (ArgList.openEval contract args state) := by
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
              apply Simulation.Interaction.AllDone.mono
                (Simulation.Interaction.Successful.bind_inv hFnSuccess)
              intro callDone hDone
              cases callDone <;> exact hDone

/-- One positive-fuel guarded loop iteration, exposed from the canonical
parameterized Functions control semantics. -/
theorem openRunForLoop_succ
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (loopCtx : Functions.Source.Ctx) (cond : Functions.Expr 1)
    (postBase : Functions.Source.Ctx) (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx) (body : Functions.Block)
    (fuel : Nat) (state : State) :
    openRunForLoop contract program loopCtx cond postBase post bodyBase body
        (fuel + 1) state =
      Simulation.Interaction.bind
        (Expr.openEvalCondition contract cond state)
        (fun result =>
          if result.2 then
            Simulation.Interaction.bind
              (Block.openRunScoped contract program bodyBase body fuel result.1)
              (fun bodyOutcome =>
                match bodyOutcome.mode with
                | .brk =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        bodyOutcome.state)
                | .regular | .cont =>
                    Simulation.Interaction.bind
                      (Block.openRunScoped contract program postBase post fuel
                        bodyOutcome.state)
                      (fun postOutcome =>
                        match postOutcome.mode with
                        | .regular =>
                            openRunForLoop contract program loopCtx cond
                              postBase post bodyBase body fuel
                              postOutcome.state
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
  unfold openRunForLoop
  simp only [Functions.Source.Effectful.Control.Stmt.runForLoop]
  rfl

/-- A successful guarded loop kernel is exactly the ordinary canonical loop
kernel, including the ordered open interaction tree. -/
theorem openRunForLoop_eq_ordinary_of_successful
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (loopCtx : Functions.Source.Ctx) (cond : Functions.Expr 1)
    (postBase : Functions.Source.Ctx) (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx) (body : Functions.Block)
    (fuel : Nat) (state : State)
    (hSuccessful : Simulation.Interaction.Successful
      (openRunForLoop contract program loopCtx cond postBase post bodyBase body
        fuel state)) :
    openRunForLoop contract program loopCtx cond postBase post bodyBase body
        fuel state =
      Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx cond
        postBase post bodyBase body fuel state := by
  exact
    Functions.InteractionRefinement.Stmt.runForLoop_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract) program loopCtx cond
      postBase post bodyBase body fuel state hSuccessful

/-- The positive-fuel guarded `for` wrapper exposes its initializer and loop
kernel while retaining the canonical Functions control semantics. -/
theorem openRun_for
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (init : Functions.Block)
    (cond : Functions.Expr 1) (post body : Functions.Block) (state : State) :
    openRun contract program ctx (fuel + 1) (.for_ init cond post body) state =
      Simulation.Interaction.bind
        (Block.openRun contract program ctx.withoutLoopControl fuel init state)
        (fun initResult =>
          match initResult.1.mode with
          | .regular =>
              Simulation.Interaction.bind
                (openRunForLoop contract program initResult.2 cond
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

/-- A successful guarded statement run is exactly the ordinary canonical
statement run. -/
theorem openRun_eq_ordinary_of_successful
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (stmt : Functions.Stmt)
    (state : State)
    (hSuccessful : Simulation.Interaction.Successful
      (openRun contract program ctx fuel stmt state)) :
    openRun contract program ctx fuel stmt state =
      Functions.InteractionSemantics.Stmt.openRun
        program ctx fuel stmt state := by
  exact
    Functions.InteractionRefinement.Stmt.run_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract) program ctx fuel stmt state
      hSuccessful

theorem openRun_let
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (name : Functions.Name)
    (value : Functions.Expr 1) (state : State) :
    openRun contract program ctx fuel (.let_ name value) state =
      Simulation.Interaction.bind (Expr.openEvalOne contract value state)
        (fun result =>
          Simulation.Interaction.pure
            (Functions.Source.Effectful.Outcome.regular
              (result.1.insert name result.2),
              { ctx with scope := name :: ctx.scope })) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run,
    Expr.openEvalOne,
    Locals.Source.Effectful.Expr.Control.evalOne,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.insert]
  rfl

theorem openRun_expr
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (expr : Functions.Expr 0) (state : State) :
    openRun contract program ctx fuel (.expr expr) state =
      Simulation.Interaction.bind (Expr.openEval contract expr state)
        (fun result =>
          Simulation.Interaction.pure
            (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run Expr.openEval
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  rfl

theorem openRun_assign_of_contains
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (name : Functions.Name)
    (value : Functions.Expr 1) (state : State)
    (hContains : state.vars.contains name = true) :
    openRun contract program ctx fuel (.assign name value) state =
      Simulation.Interaction.bind (Expr.openEvalOne contract value state)
        (fun result =>
          Simulation.Interaction.pure
            (Functions.Source.Effectful.Outcome.regular
              (result.1.insert name result.2), ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, id_eq, hContains,
    ↓reduceIte, Expr.openEvalOne,
    Locals.Source.Effectful.Expr.Control.evalOne,
    Locals.Source.Effectful.StateModel.withVars,
    Locals.Source.State.withVars,
    Locals.Source.Effectful.StateModel.insert]
  rfl

theorem openRun_brk
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (state : State)
    {scope : List Functions.Name}
    (hScope : ctx.breakScope? = some scope) :
    openRun contract program ctx fuel .brk state =
      Simulation.Interaction.pure
        (Functions.Source.Effectful.Outcome.brk
          (state.restrictTo scope), ctx) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run, hScope,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]
  rfl

theorem openRun_cont
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (state : State)
    {scope : List Functions.Name}
    (hScope : ctx.continueScope? = some scope) :
    openRun contract program ctx fuel .cont state =
      Simulation.Interaction.pure
        (Functions.Source.Effectful.Outcome.cont
          (state.restrictTo scope), ctx) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run, hScope,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]
  rfl

theorem openRun_leave
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (state : State)
    {scope : List Functions.Name}
    (hScope : ctx.leaveScope? = some scope) :
    openRun contract program ctx fuel .leave state =
      Simulation.Interaction.pure
        (Functions.Source.Effectful.Outcome.leave
          (state.restrictTo scope), ctx) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run, hScope,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.restrictTo]
  rfl

end Stmt

namespace Block

/-- A successful guarded block run is exactly the ordinary canonical block
run, including every query, answer continuation, terminal outcome, and state. -/
theorem openRun_eq_ordinary_of_successful
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (block : Functions.Block)
    (state : State)
    (hSuccessful : ExecutionSafe contract program ctx fuel block state) :
    openRun contract program ctx fuel block state =
      Functions.InteractionSemantics.Block.openRun
        program ctx fuel block state := by
  exact
    Functions.InteractionRefinement.Block.runOpen_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract)
      program ctx fuel block state hSuccessful

theorem ExecutionSafe.ordinarySuccessful
    {contract : MemoryContract.Contract} {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {fuel : Nat} {block : Functions.Block}
    {state : State}
    (hSafe : ExecutionSafe contract program ctx fuel block state) :
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Block.openRun
        program ctx fuel block state) := by
  rw [← openRun_eq_ordinary_of_successful
    contract program ctx fuel block state hSafe]
  exact hSafe

theorem openRun_cons
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt) (state : State) :
    openRun contract program ctx (fuel + 1)
        { stmts := stmt :: rest } state =
      Simulation.Interaction.bind
        (Stmt.openRun contract program ctx fuel stmt state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              openRun contract program result.2 fuel
                { stmts := rest } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) := by
  change
    Functions.Source.Effectful.Control.Block.runOpen
        Functions.InteractionSemantics.stateModel
        (primitiveSemantics contract) program ctx (fuel + 1)
        { stmts := stmt :: rest } state = _
  rw [Nat.add_one]
  simp only [Functions.Source.Effectful.Control.Block.runOpen]
  rfl

theorem openRun_nil
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (state : State) :
    openRun contract program ctx (fuel + 1) { stmts := [] } state =
      (pure (Functions.Source.Effectful.Outcome.regular state, ctx) :
        Open (Outcome × Functions.Source.Ctx)) := by
  change
    Functions.Source.Effectful.Control.Block.runOpen
        Functions.InteractionSemantics.stateModel
        (primitiveSemantics contract) program ctx (fuel + 1)
        { stmts := [] } state = _
  rw [Nat.add_one]
  simp only [Functions.Source.Effectful.Control.Block.runOpen]

theorem openRun_append
    (contract : MemoryContract.Contract) (program : Functions.Program) :
    ∀ (left right : List Functions.Stmt) (ctx : Functions.Source.Ctx)
      (fuel : Nat) (state : State),
      openRun contract program ctx fuel { stmts := left ++ right } state =
        Simulation.Interaction.bind
          (openRun contract program ctx fuel { stmts := left } state)
          (fun result =>
            match result.1.mode with
            | .regular =>
                openRun contract program result.2 (fuel - left.length)
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
          rw [show stmt :: rest ++ right = stmt :: (rest ++ right) by rfl,
            openRun_cons, openRun_cons]
          simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]
          rw [Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Stmt.openRun contract program ctx fuel stmt state))
          intro outcome _
          cases hMode : outcome.1.mode with
          | regular =>
              simpa [hMode] using
                (ih right outcome.2 fuel outcome.1.state)
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

theorem openRunScoped_eq_ordinary_of_successful
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (block : Functions.Block) (fuel : Nat)
    (state : State)
    (hSuccessful : Simulation.Interaction.Successful
      (openRunScoped contract program ctx block fuel state)) :
    openRunScoped contract program ctx block fuel state =
      Functions.InteractionSemantics.Block.openRunScoped
        program ctx block fuel state := by
  exact
    Functions.InteractionRefinement.Block.runScoped_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract)
      program ctx block fuel state hSuccessful

end Block

namespace Stmt

/-- A guarded lexical block restricts state only after regular completion. -/
theorem openRun_block
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (body : Functions.Block) (state : State) :
    openRun contract program ctx fuel (.block body) state =
      Simulation.Interaction.bind
        (Block.openRun contract program ctx fuel body state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (Functions.InteractionSemantics.stateModel.restrictTo
                    ctx.scope result.1.state), ctx)
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
            Functions.InteractionSemantics.stateModel
            (primitiveSemantics contract) program ctx fuel body state)
          (fun result =>
            match result.1.mode with
            | .regular =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular
                    (Functions.InteractionSemantics.stateModel.restrictTo
                      ctx.scope result.1.state))
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure result.1))
        (fun outcome => Simulation.Interaction.pure (outcome, ctx)) = _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.Source.Effectful.Control.Block.runOpen
        Functions.InteractionSemantics.stateModel
        (primitiveSemantics contract) program ctx fuel body state))
  intro result _
  cases hMode : result.1.mode <;> rfl

/-- A guarded positive-fuel conditional exposes its selected branch. -/
theorem openRun_if
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block) (state : State) :
    openRun contract program ctx (fuel + 1) (.if_ cond body) state =
      Simulation.Interaction.bind
        (Expr.openEvalCondition contract cond state)
        (fun result =>
          if result.2 then
            openRun contract program ctx fuel (.block body) result.1
          else
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Expr.openEvalCondition
  rfl

/-- A guarded positive-fuel switch exposes its scrutinee and branch. -/
theorem openRun_switch
    (contract : MemoryContract.Contract) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block) (state : State) :
    openRun contract program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) state =
      Simulation.Interaction.bind
        (Expr.openEvalOne contract scrutinee state)
        (fun result =>
          match Functions.Source.Switch.select
              result.2 cases defaultBody with
          | some body =>
              openRun contract program ctx fuel (.block body) result.1
          | none =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Expr.openEvalOne
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.Source.Effectful.Expr.Control.evalOne
        Functions.InteractionSemantics.stateModel
        (primitiveSemantics contract) scrutinee state))
  intro result _
  cases Functions.Source.Switch.select result.2 cases defaultBody <;> rfl

end Stmt

namespace Program

noncomputable def openRunState (contract : MemoryContract.Contract)
    (fuel : Nat) (program : Functions.Program) (state : State) : Open Outcome :=
  Functions.Source.Canonical.Program.runState
    Functions.InteractionSemantics.stateModel
    (primitiveSemantics contract) fuel program state

/-- Source-facing reservation safety for one concrete program execution. The
`Successful` quantifier still ranges over every answer branch of that open
execution, but says nothing about unrelated expressions or states. -/
def ExecutionSafe (contract : MemoryContract.Contract) (fuel : Nat)
    (program : Functions.Program) (state : State) : Prop :=
  Simulation.Interaction.Successful
    (openRunState contract fuel program state)

theorem openRunState_eq_ordinary_of_executionSafe
    (contract : MemoryContract.Contract) (fuel : Nat)
    (program : Functions.Program) (state : State)
    (hSafe : ExecutionSafe contract fuel program state) :
    openRunState contract fuel program state =
      Functions.InteractionSemantics.Program.openRunState
        fuel program state := by
  exact
    Functions.InteractionRefinement.Program.runState_eq_of_successRefines
      Functions.InteractionSemantics.stateModel
      (primitive_successRefines_ordinary contract)
      fuel program state hSafe

end Program

end AllocationInteractionSafeSemantics
end Functions
end EvmCompiler
