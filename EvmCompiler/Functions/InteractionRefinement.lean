import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Locals.InteractionRefinement

/-!
Successful refinement for the canonical parameterized Functions control
interpreter under open interactions. Control is not reimplemented here: these
theorems prove that changing only the primitive capability leaves every
successful interaction tree unchanged.
-/

namespace EvmCompiler
namespace Functions
namespace InteractionRefinement

abbrev Open (alpha : Type) := Simulation.Interaction EVMException alpha
abbrev PrimitiveSemantics (state : Type) :=
  Functions.Source.Effectful.Control.PrimitiveSemantics Open state
abbrev SuccessRefines {state : Type} :=
  @Locals.InteractionRefinement.PrimitiveSemantics.SuccessRefines state

namespace ArgList

theorem eval_eq_of_successRefines
    {state : Type} (model : Functions.Source.Effectful.StateModel state)
    {sourcePrim targetPrim : PrimitiveSemantics state}
    (hRefines : SuccessRefines sourcePrim targetPrim) :
    forall (args : List (Functions.Expr 1)) (initial : state),
      Simulation.Interaction.Successful
          (Functions.Source.Effectful.ArgList.Control.eval
            model sourcePrim args initial) ->
        Functions.Source.Effectful.ArgList.Control.eval
            model sourcePrim args initial =
          Functions.Source.Effectful.ArgList.Control.eval
            model targetPrim args initial := by
  intro args
  induction args with
  | nil =>
      intro initial _hSuccessful
      rfl
  | cons arg rest ih =>
      intro initial hSuccessful
      unfold Functions.Source.Effectful.ArgList.Control.eval
      apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
      · exact
          Locals.InteractionRefinement.Expr.evalOne_eq_of_successRefines
            model hRefines arg initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
      · intro argResult hRestSuccessful
        apply Locals.InteractionRefinement.bind_eq_of_successful
          hRestSuccessful
        · exact ih argResult.1
            (Simulation.Interaction.Successful.bind_left hRestSuccessful)
        · intro _restResult _hPure
          rfl

end ArgList

open Functions.Source.Effectful

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpen_eq_of_successRefines
      {state : Type} (model : StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : SuccessRefines sourcePrim targetPrim)
      (program : Functions.Program) :
      forall (ctx : Functions.Source.Ctx) (fuel : Nat)
        (block : Functions.Block) (initial : state),
        Simulation.Interaction.Successful
            (Control.Block.runOpen model sourcePrim program ctx fuel block
              initial) ->
          Control.Block.runOpen model sourcePrim program ctx fuel block
              initial =
            Control.Block.runOpen model targetPrim program ctx fuel block
              initial := by
    intro ctx fuel block initial hSuccessful
    cases fuel with
    | zero =>
        simp [Control.Block.runOpen]
    | succ fuel =>
        rcases block with ⟨stmts⟩
        cases stmts with
        | nil =>
            simp [Control.Block.runOpen]
        | cons stmt rest =>
            simp only [Control.Block.runOpen] at hSuccessful ⊢
            apply Locals.InteractionRefinement.bind_eq_of_successful
              hSuccessful
            · exact Stmt.run_eq_of_successRefines model hRefines program ctx
                fuel stmt initial
                (Simulation.Interaction.Successful.bind_left hSuccessful)
            · intro stmtResult hRestSuccessful
              rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
              cases hMode : stmtOutcome.mode with
              | regular =>
                  simp only [hMode] at hRestSuccessful ⊢
                  exact Block.runOpen_eq_of_successRefines model hRefines
                    program stmtCtx fuel { stmts := rest }
                    stmtOutcome.state hRestSuccessful
              | brk => simp [hMode]
              | cont => simp [hMode]
              | leave => simp [hMode]
              | halt kind => simp [hMode]
  termination_by
    ctx fuel block initial hSuccessful => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_eq_of_successRefines
      {state : Type} (model : StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : SuccessRefines sourcePrim targetPrim)
      (program : Functions.Program) :
      forall (ctx : Functions.Source.Ctx) (block : Functions.Block)
        (fuel : Nat) (initial : state),
        Simulation.Interaction.Successful
            (Control.Block.runScoped model sourcePrim program ctx block fuel
              initial) ->
          Control.Block.runScoped model sourcePrim program ctx block fuel
              initial =
            Control.Block.runScoped model targetPrim program ctx block fuel
              initial := by
    intro ctx block fuel initial hSuccessful
    unfold Control.Block.runScoped at hSuccessful ⊢
    apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
    · exact Block.runOpen_eq_of_successRefines model hRefines program ctx fuel
        block initial
        (Simulation.Interaction.Successful.bind_left hSuccessful)
    · intro _result _hContinuation
      rfl
  termination_by
    ctx block fuel initial hSuccessful => (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right fuel
          (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  theorem FunDef.runBody_eq_of_successRefines
      {state : Type} (model : StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : SuccessRefines sourcePrim targetPrim)
      (program : Functions.Program) :
      forall (fn : Functions.FunDef) (args : List Word) (fuel : Nat)
        (initial : state),
        Simulation.Interaction.Successful
            (Control.FunDef.runBody model sourcePrim program fn args fuel
              initial) ->
          Control.FunDef.runBody model sourcePrim program fn args fuel
              initial =
            Control.FunDef.runBody model targetPrim program fn args fuel
              initial := by
    intro fn args fuel initial hSuccessful
    cases fuel with
    | zero =>
        simp [Control.FunDef.runBody]
    | succ fuel =>
        unfold Control.FunDef.runBody at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · rfl
        · intro paramStore hAfterParams
          apply Locals.InteractionRefinement.bind_eq_of_successful
            hAfterParams
          · exact Block.runOpen_eq_of_successRefines model hRefines program
              { Functions.Source.Ctx.initial.withLeaveScope
                  (fn.returns ++ fn.params) with
                scope := fn.returns ++ fn.params }
              fuel fn.body
              (model.withSource initial
                { shared := (model.source initial).shared
                  vars := Functions.Source.Store.initReturns fn.returns
                    paramStore })
              (Simulation.Interaction.Successful.bind_left hAfterParams)
          · intro _bodyResult _hContinuation
            rfl
  termination_by
    fn args fuel initial hSuccessful => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_eq_of_successRefines
      {state : Type} (model : StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : SuccessRefines sourcePrim targetPrim)
      (program : Functions.Program) :
      forall (loopCtx : Functions.Source.Ctx) (cond : Functions.Expr 1)
        (postBase : Functions.Source.Ctx) (post : Functions.Block)
        (bodyBase : Functions.Source.Ctx) (body : Functions.Block)
        (fuel : Nat) (initial : state),
        Simulation.Interaction.Successful
            (Control.Stmt.runForLoop model sourcePrim program loopCtx cond
              postBase post bodyBase body fuel initial) ->
          Control.Stmt.runForLoop model sourcePrim program loopCtx cond
              postBase post bodyBase body fuel initial =
            Control.Stmt.runForLoop model targetPrim program loopCtx cond
              postBase post bodyBase body fuel initial := by
    intro loopCtx cond postBase post bodyBase body fuel initial hSuccessful
    cases fuel with
    | zero =>
        simp [Control.Stmt.runForLoop]
    | succ fuel =>
        unfold Control.Stmt.runForLoop at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · exact
            Locals.InteractionRefinement.Expr.evalCondition_eq_of_successRefines
              model hRefines cond initial
              (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro condResult hAfterCond
          rcases condResult with ⟨stateAfterCond, condTrue⟩
          cases condTrue with
          | false => simp
          | true =>
              simp only [Bool.if_true_right] at hAfterCond ⊢
              apply Locals.InteractionRefinement.bind_eq_of_successful
                hAfterCond
              · exact Block.runScoped_eq_of_successRefines model hRefines
                  program bodyBase body fuel stateAfterCond
                  (Simulation.Interaction.Successful.bind_left hAfterCond)
              · intro bodyOutcome hAfterBody
                cases hBodyMode : bodyOutcome.mode with
                | brk => simp [hBodyMode]
                | leave => simp [hBodyMode]
                | halt kind => simp [hBodyMode]
                | regular =>
                    simp only [hBodyMode] at hAfterBody ⊢
                    apply Locals.InteractionRefinement.bind_eq_of_successful
                      hAfterBody
                    · exact Block.runScoped_eq_of_successRefines model hRefines
                        program postBase post fuel bodyOutcome.state
                        (Simulation.Interaction.Successful.bind_left hAfterBody)
                    · intro postOutcome hAfterPost
                      cases hPostMode : postOutcome.mode with
                      | regular =>
                          simp only [hPostMode] at hAfterPost ⊢
                          exact Stmt.runForLoop_eq_of_successRefines model
                            hRefines program loopCtx cond postBase post bodyBase
                            body fuel postOutcome.state hAfterPost
                      | brk => simp [hPostMode]
                      | cont => simp [hPostMode]
                      | leave => simp [hPostMode]
                      | halt kind => simp [hPostMode]
                | cont =>
                    simp only [hBodyMode] at hAfterBody ⊢
                    apply Locals.InteractionRefinement.bind_eq_of_successful
                      hAfterBody
                    · exact Block.runScoped_eq_of_successRefines model hRefines
                        program postBase post fuel bodyOutcome.state
                        (Simulation.Interaction.Successful.bind_left hAfterBody)
                    · intro postOutcome hAfterPost
                      cases hPostMode : postOutcome.mode with
                      | regular =>
                          simp only [hPostMode] at hAfterPost ⊢
                          exact Stmt.runForLoop_eq_of_successRefines model
                            hRefines program loopCtx cond postBase post bodyBase
                            body fuel postOutcome.state hAfterPost
                      | brk => simp [hPostMode]
                      | cont => simp [hPostMode]
                      | leave => simp [hPostMode]
                      | halt kind => simp [hPostMode]
  termination_by
    loopCtx cond postBase post bodyBase body fuel initial hSuccessful =>
      (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_eq_of_successRefines
      {state : Type} (model : StateModel state)
      {sourcePrim targetPrim : PrimitiveSemantics state}
      (hRefines : SuccessRefines sourcePrim targetPrim)
      (program : Functions.Program) :
      forall (ctx : Functions.Source.Ctx) (fuel : Nat)
        (stmt : Functions.Stmt) (initial : state),
        Simulation.Interaction.Successful
            (Control.Stmt.run model sourcePrim program ctx fuel stmt initial) ->
          Control.Stmt.run model sourcePrim program ctx fuel stmt initial =
            Control.Stmt.run model targetPrim program ctx fuel stmt initial := by
    intro ctx fuel stmt initial hSuccessful
    cases stmt with
    | expr expr =>
        unfold Control.Stmt.run at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · exact Locals.InteractionRefinement.Expr.eval_eq_of_successRefines
            model hRefines expr initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro _result _hContinuation
          rfl
    | let_ name value =>
        unfold Control.Stmt.run at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · exact Locals.InteractionRefinement.Expr.evalOne_eq_of_successRefines
            model hRefines value initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro _result _hContinuation
          rfl
    | assign name value =>
        unfold Control.Stmt.run at hSuccessful ⊢
        by_cases hContains : (model.vars initial).contains name
        · simp only [hContains, Bool.true_eq, ↓reduceIte] at hSuccessful ⊢
          apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
          · exact
              Locals.InteractionRefinement.Expr.evalOne_eq_of_successRefines
                model hRefines value initial
                (Simulation.Interaction.Successful.bind_left hSuccessful)
          · intro _result _hContinuation
            rfl
        · simp [hContains]
    | block body =>
        unfold Control.Stmt.run at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · exact Block.runScoped_eq_of_successRefines model hRefines program ctx
            body fuel initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro _outcome _hContinuation
          rfl
    | if_ cond body =>
        cases fuel with
        | zero => simp [Control.Stmt.run]
        | succ fuel =>
            unfold Control.Stmt.run at hSuccessful ⊢
            apply Locals.InteractionRefinement.bind_eq_of_successful
              hSuccessful
            · exact Locals.InteractionRefinement.Expr.evalCondition_eq_of_successRefines
                model hRefines cond initial
                (Simulation.Interaction.Successful.bind_left hSuccessful)
            · intro condResult hAfterCond
              rcases condResult with ⟨stateAfterCond, condTrue⟩
              cases condTrue with
              | false => simp
              | true =>
                  simp only [Bool.if_true_right] at hAfterCond ⊢
                  apply Locals.InteractionRefinement.bind_eq_of_successful
                    hAfterCond
                  · exact Block.runScoped_eq_of_successRefines model hRefines
                      program ctx body fuel stateAfterCond
                      (Simulation.Interaction.Successful.bind_left hAfterCond)
                  · intro _outcome _hContinuation
                    rfl
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero => simp [Control.Stmt.run]
        | succ fuel =>
            unfold Control.Stmt.run at hSuccessful ⊢
            apply Locals.InteractionRefinement.bind_eq_of_successful
              hSuccessful
            · exact Locals.InteractionRefinement.Expr.evalOne_eq_of_successRefines
                model hRefines scrutinee initial
                (Simulation.Interaction.Successful.bind_left hSuccessful)
            · intro scrutineeResult hAfterScrutinee
              rcases scrutineeResult with ⟨stateAfterScrutinee, value⟩
              cases hSelected : Functions.Source.Switch.select
                  value cases defaultBody with
              | none => simp [hSelected]
              | some selected =>
                  simp only [hSelected] at hAfterScrutinee ⊢
                  apply Locals.InteractionRefinement.bind_eq_of_successful
                    hAfterScrutinee
                  · exact Block.runScoped_eq_of_successRefines model hRefines
                      program ctx selected fuel stateAfterScrutinee
                      (Simulation.Interaction.Successful.bind_left
                        hAfterScrutinee)
                  · intro _outcome _hContinuation
                    rfl
    | for_ init cond post body =>
        cases fuel with
        | zero => simp [Control.Stmt.run]
        | succ fuel =>
            unfold Control.Stmt.run at hSuccessful ⊢
            apply Locals.InteractionRefinement.bind_eq_of_successful
              hSuccessful
            · exact Block.runOpen_eq_of_successRefines model hRefines program
                ctx.withoutLoopControl fuel init initial
                (Simulation.Interaction.Successful.bind_left hSuccessful)
            · intro initResult hAfterInit
              rcases initResult with ⟨initOutcome, initCtx⟩
              cases hInitMode : initOutcome.mode with
              | regular =>
                  simp only [hInitMode] at hAfterInit ⊢
                  apply Locals.InteractionRefinement.bind_eq_of_successful
                    hAfterInit
                  · exact Stmt.runForLoop_eq_of_successRefines model hRefines
                      program initCtx cond
                      initCtx.withoutLoopControl post
                      (initCtx.withLoopControl initCtx.scope initCtx.scope)
                      body fuel initOutcome.state
                      (Simulation.Interaction.Successful.bind_left hAfterInit)
                  · intro _loopOutcome _hContinuation
                    rfl
              | brk => simp [hInitMode]
              | cont => simp [hInitMode]
              | leave => simp [hInitMode]
              | halt kind => simp [hInitMode]
    | brk => simp [Control.Stmt.run]
    | cont => simp [Control.Stmt.run]
    | leave => simp [Control.Stmt.run]
    | call targets functionName args =>
        cases fuel with
        | zero => simp [Control.Stmt.run]
        | succ fuel =>
            unfold Control.Stmt.run at hSuccessful ⊢
            by_cases hTargets : targets.Nodup
            · simp only [hTargets, ↓reduceIte] at hSuccessful ⊢
              apply Locals.InteractionRefinement.bind_eq_of_successful
                hSuccessful
              · exact ArgList.eval_eq_of_successRefines model hRefines args
                  initial
                  (Simulation.Interaction.Successful.bind_left hSuccessful)
              · intro argResult hAfterArgs
                rcases argResult with ⟨stateAfterArgs, argValues⟩
                apply Locals.InteractionRefinement.bind_eq_of_successful
                  hAfterArgs
                · rfl
                · intro fn hAfterFind
                  apply Locals.InteractionRefinement.bind_eq_of_successful
                    hAfterFind
                  · exact FunDef.runBody_eq_of_successRefines model hRefines
                      program fn argValues fuel stateAfterArgs
                      (Simulation.Interaction.Successful.bind_left hAfterFind)
                  · intro callResult _hAfterCall
                    cases callResult with
                    | halted kind haltedState => rfl
                    | returned stateAfterCall returnValues =>
                        rfl
            · simp only [hTargets, ↓reduceIte]
    | terminal kind =>
        unfold Control.Stmt.run at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · exact hRefines.terminal kind initial []
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro _final _hContinuation
          rfl
    | terminalArgs kind args =>
        unfold Control.Stmt.run at hSuccessful ⊢
        apply Locals.InteractionRefinement.bind_eq_of_successful hSuccessful
        · exact Locals.InteractionRefinement.Expr.ExprSeq.eval_eq_of_successRefines
            model hRefines args initial
            (Simulation.Interaction.Successful.bind_left hSuccessful)
        · intro argResult hAfterArgs
          rcases argResult with ⟨stateAfterArgs, values⟩
          apply Locals.InteractionRefinement.bind_eq_of_successful hAfterArgs
          · exact hRefines.terminal kind stateAfterArgs values
              (Simulation.Interaction.Successful.bind_left hAfterArgs)
          · intro _final _hContinuation
            rfl
  termination_by
    ctx fuel stmt initial hSuccessful => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
end

namespace Program

theorem runState_eq_of_successRefines
    {state : Type} (model : StateModel state)
    {sourcePrim targetPrim : PrimitiveSemantics state}
    (hRefines : SuccessRefines sourcePrim targetPrim)
    (fuel : Nat) (program : Functions.Program) (initial : state)
    (hSuccessful : Simulation.Interaction.Successful
      (Control.Program.runState model sourcePrim fuel program initial)) :
    Control.Program.runState model sourcePrim fuel program initial =
      Control.Program.runState model targetPrim fuel program initial := by
  unfold Control.Program.runState
  exact Block.runScoped_eq_of_successRefines model hRefines program
    Functions.Source.Ctx.initial program.body fuel initial hSuccessful

end Program

end InteractionRefinement
end Functions
end EvmCompiler
