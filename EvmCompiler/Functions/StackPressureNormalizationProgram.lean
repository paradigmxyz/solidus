import EvmCompiler.Functions.StackPressureNormalization

namespace EvmCompiler.Functions.StackPressureNormalization

mutual
  theorem Block.normalize_openRun
      (program : Program) (ctx : Functions.Source.Ctx)
      (fuel : Nat) (block : Block)
      (state : Functions.InteractionSemantics.State) :
      Functions.InteractionSemantics.Block.openRun
          (Program.normalize program) ctx fuel (Block.normalize block) state =
        Functions.InteractionSemantics.Block.openRun
          program ctx fuel block state := by
    cases fuel with
    | zero =>
        simp [Functions.InteractionSemantics.Block.openRun,
          Functions.Source.Canonical.Block.runOpen,
          Functions.Source.Effectful.Control.Block.runOpen]
    | succ fuel =>
        rcases block with ⟨stmts⟩
        cases stmts with
        | nil =>
            simp [Block.normalize, StmtList.normalize,
              Functions.InteractionSemantics.Block.openRun,
              Functions.Source.Canonical.Block.runOpen,
              Functions.Source.Effectful.Control.Block.runOpen]
        | cons stmt rest =>
            simp only [Block.normalize, StmtList.normalize]
            unfold Functions.InteractionSemantics.Block.openRun
              Functions.Source.Canonical.Block.runOpen
              Functions.Source.Effectful.Control.Block.runOpen
            change Simulation.Interaction.bind
                (Functions.InteractionSemantics.Stmt.openRun
                  (Program.normalize program) ctx fuel
                  (Stmt.normalize stmt) state)
                (fun result =>
                  match result.1.mode with
                  | .regular =>
                      Functions.InteractionSemantics.Block.openRun
                        (Program.normalize program) result.2 fuel
                        (Block.normalize { stmts := rest }) result.1.state
                  | .brk | .cont | .leave | .halt _ =>
                      Simulation.Interaction.pure (result.1, ctx)) = _
            rw [EvmCompiler.Functions.StackPressureNormalization.Stmt.normalize_openRun]
            apply Simulation.Interaction.AllDone.bind_congr
              (Simulation.Interaction.AllDone.trivial _)
            intro result _
            cases hMode : result.1.mode <;>
              simp only [hMode]
            · exact Block.normalize_openRun program result.2 fuel
                { stmts := rest } result.1.state
            all_goals rfl
  termination_by (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.normalize_openRunScoped
      (program : Program) (ctx : Functions.Source.Ctx)
      (block : Block) (fuel : Nat)
      (state : Functions.InteractionSemantics.State) :
      Functions.InteractionSemantics.Block.openRunScoped
          (Program.normalize program) ctx (Block.normalize block) fuel state =
        Functions.InteractionSemantics.Block.openRunScoped
          program ctx block fuel state := by
    unfold Functions.InteractionSemantics.Block.openRunScoped
      Functions.Source.Canonical.Block.runScoped
      Functions.Source.Effectful.Control.Block.runScoped
    change Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun
          (Program.normalize program) ctx fuel (Block.normalize block) state) _ =
      Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun
          program ctx fuel block state) _
    rw [Block.normalize_openRun]
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  theorem FunDef.normalize_openRunBody
      (program : Program) (fn : FunDef) (args : List Word)
      (fuel : Nat) (state : Functions.InteractionSemantics.State) :
      Functions.InteractionSemantics.FunDef.openRunBody
          (Program.normalize program) (FunDef.normalize fn) args fuel state =
        Functions.InteractionSemantics.FunDef.openRunBody
          program fn args fuel state := by
    cases fuel with
    | zero =>
        simp [Functions.InteractionSemantics.FunDef.openRunBody,
          Functions.Source.Canonical.FunDef.runBody,
          Functions.Source.Effectful.Control.FunDef.runBody]
    | succ fuel =>
        unfold Functions.InteractionSemantics.FunDef.openRunBody
          Functions.Source.Canonical.FunDef.runBody
          Functions.Source.Effectful.Control.FunDef.runBody
        simp only [FunDef.normalize]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial _)
        intro paramStore _
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Block.openRun
              (Program.normalize program)
              { (Functions.Source.Ctx.initial.withLeaveScope
                    (fn.returns ++ fn.params)) with
                scope := fn.returns ++ fn.params }
              fuel (Block.normalize fn.body)
              (Functions.InteractionSemantics.stateModel.withSource state
                { shared :=
                    (Functions.InteractionSemantics.stateModel.source state).shared,
                  vars := Functions.Source.Store.initReturns
                    fn.returns paramStore })) _ =
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Block.openRun
              program
              { (Functions.Source.Ctx.initial.withLeaveScope
                    (fn.returns ++ fn.params)) with
                scope := fn.returns ++ fn.params }
              fuel fn.body
              (Functions.InteractionSemantics.stateModel.withSource state
                { shared :=
                    (Functions.InteractionSemantics.stateModel.source state).shared,
                  vars := Functions.Source.Store.initReturns
                    fn.returns paramStore })) _
        rw [Block.normalize_openRun]
  termination_by (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.normalize_openRunForLoop
      (program : Program) (loopCtx : Functions.Source.Ctx)
      (cond : Expr 1) (postBase : Functions.Source.Ctx) (post : Block)
      (bodyBase : Functions.Source.Ctx) (body : Block)
      (fuel : Nat) (state : Functions.InteractionSemantics.State) :
      Functions.InteractionSemantics.Stmt.openRunForLoop
          (Program.normalize program) loopCtx (Expr.normalize cond)
          postBase (Block.normalize post) bodyBase (Block.normalize body)
          fuel state =
      Functions.InteractionSemantics.Stmt.openRunForLoop
          program loopCtx cond postBase post bodyBase body fuel state := by
    cases fuel with
    | zero =>
        simp [Functions.InteractionSemantics.Stmt.openRunForLoop,
          Functions.Source.Canonical.Stmt.runForLoop,
          Functions.Source.Effectful.Control.Stmt.runForLoop]
    | succ fuel =>
        unfold Functions.InteractionSemantics.Stmt.openRunForLoop
          Functions.Source.Canonical.Stmt.runForLoop
          Functions.Source.Effectful.Control.Stmt.runForLoop
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalCondition
              (Expr.normalize cond) state)
            (fun condResult =>
              if condResult.2 then
                Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Block.openRunScoped
                    (Program.normalize program) bodyBase
                    (Block.normalize body) fuel condResult.1)
                  (fun bodyOutcome =>
                    match bodyOutcome.mode with
                    | .brk =>
                        Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            bodyOutcome.state)
                    | .regular | .cont =>
                        Simulation.Interaction.bind
                          (Functions.InteractionSemantics.Block.openRunScoped
                            (Program.normalize program) postBase
                            (Block.normalize post) fuel bodyOutcome.state)
                          (fun postOutcome =>
                            match postOutcome.mode with
                            | .regular =>
                                Functions.InteractionSemantics.Stmt.openRunForLoop
                                  (Program.normalize program) loopCtx
                                  (Expr.normalize cond) postBase
                                  (Block.normalize post) bodyBase
                                  (Block.normalize body) fuel postOutcome.state
                            | .brk | .cont =>
                                Simulation.Interaction.error .InvalidInstruction
                            | .leave | .halt _ =>
                                Simulation.Interaction.pure postOutcome)
                    | .leave | .halt _ =>
                        Simulation.Interaction.pure bodyOutcome)
              else
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular
                    (Functions.InteractionSemantics.stateModel.restrictTo
                      loopCtx.scope condResult.1))) = _
        rw [Expr.normalize_openEvalCondition]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial _)
        intro condResult _
        rcases condResult with ⟨afterCond, condTrue⟩
        cases condTrue with
        | false => rfl
        | true =>
            rw [Block.normalize_openRunScoped]
            apply Simulation.Interaction.AllDone.bind_congr
              (Simulation.Interaction.AllDone.trivial _)
            intro bodyOutcome _
            cases hBodyMode : bodyOutcome.mode <;>
              simp only [hBodyMode]
            · rw [Block.normalize_openRunScoped]
              apply Simulation.Interaction.AllDone.bind_congr
                (Simulation.Interaction.AllDone.trivial _)
              intro postOutcome _
              cases hPostMode : postOutcome.mode <;>
                simp only [hPostMode]
              · exact Stmt.normalize_openRunForLoop program loopCtx cond
                  postBase post bodyBase body fuel postOutcome.state
              all_goals rfl
            · rfl
            · rw [Block.normalize_openRunScoped]
              apply Simulation.Interaction.AllDone.bind_congr
                (Simulation.Interaction.AllDone.trivial _)
              intro postOutcome _
              cases hPostMode : postOutcome.mode <;>
                simp only [hPostMode]
              · exact Stmt.normalize_openRunForLoop program loopCtx cond
                  postBase post bodyBase body fuel postOutcome.state
              all_goals rfl
            all_goals rfl
  termination_by (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.normalize_openRun
      (program : Program) (ctx : Functions.Source.Ctx)
      (fuel : Nat) (stmt : Stmt)
      (state : Functions.InteractionSemantics.State) :
      Functions.InteractionSemantics.Stmt.openRun
          (Program.normalize program) ctx fuel (Stmt.normalize stmt) state =
        Functions.InteractionSemantics.Stmt.openRun
          program ctx fuel stmt state := by
    cases stmt with
    | expr expr =>
        simp only [Stmt.normalize]
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
          Functions.Source.Effectful.Control.Stmt.run
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEval
              (Expr.normalize expr) state) _ =
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEval expr state) _
        rw [Expr.normalize_openEval]
    | let_ name value =>
        simp only [Stmt.normalize]
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
          Functions.Source.Effectful.Control.Stmt.run
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne
              (Expr.normalize value) state) _ =
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne value state) _
        rw [Expr.normalize_openEvalOne]
    | assign name value =>
        simp only [Stmt.normalize]
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
          Functions.Source.Effectful.Control.Stmt.run
        split <;> try rfl
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne
              (Expr.normalize value) state) _ =
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne value state) _
        rw [Expr.normalize_openEvalOne]
    | block body =>
        simp only [Stmt.normalize]
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
          Functions.Source.Effectful.Control.Stmt.run
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Block.openRunScoped
              (Program.normalize program) ctx (Block.normalize body)
              fuel state) _ =
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Block.openRunScoped
              program ctx body fuel state) _
        rw [Block.normalize_openRunScoped]
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
              Functions.Source.Canonical.Stmt.run,
              Functions.Source.Effectful.Control.Stmt.run]
        | succ fuel =>
            simp only [Stmt.normalize]
            unfold Functions.InteractionSemantics.Stmt.openRun
              Functions.Source.Canonical.Stmt.run
              Functions.Source.Effectful.Control.Stmt.run
            change Simulation.Interaction.bind
                (Functions.InteractionSemantics.Expr.openEvalCondition
                  (Expr.normalize cond) state)
                (fun condResult =>
                  if condResult.2 then
                    Simulation.Interaction.bind
                      (Functions.InteractionSemantics.Block.openRunScoped
                        (Program.normalize program) ctx (Block.normalize body)
                        fuel condResult.1)
                      (fun outcome => Simulation.Interaction.pure (outcome, ctx))
                  else
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular condResult.1,
                        ctx)) = _
            rw [Expr.normalize_openEvalCondition]
            apply Simulation.Interaction.AllDone.bind_congr
              (Simulation.Interaction.AllDone.trivial _)
            intro condResult _
            rcases condResult with ⟨afterCond, condTrue⟩
            cases condTrue with
            | false => rfl
            | true =>
                rw [Block.normalize_openRunScoped]
                rfl
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
              Functions.Source.Canonical.Stmt.run,
              Functions.Source.Effectful.Control.Stmt.run]
        | succ fuel =>
            simp only [Stmt.normalize]
            unfold Functions.InteractionSemantics.Stmt.openRun
              Functions.Source.Canonical.Stmt.run
              Functions.Source.Effectful.Control.Stmt.run
            change Simulation.Interaction.bind
                (Functions.InteractionSemantics.Expr.openEvalOne
                  (Expr.normalize scrutinee) state)
                (fun result =>
                  match Functions.Source.Switch.select result.2
                      (CaseList.normalize cases)
                      (Default.normalize defaultBody) with
                  | none =>
                      Simulation.Interaction.pure
                        (Functions.Source.Effectful.Outcome.regular result.1,
                          ctx)
                  | some selected =>
                      Simulation.Interaction.bind
                        (Functions.InteractionSemantics.Block.openRunScoped
                          (Program.normalize program) ctx selected fuel result.1)
                        (fun outcome =>
                          Simulation.Interaction.pure (outcome, ctx))) = _
            rw [Expr.normalize_openEvalOne]
            apply Simulation.Interaction.AllDone.bind_congr
              (Simulation.Interaction.AllDone.trivial _)
            intro result _
            rcases result with ⟨afterScrutinee, value⟩
            rw [EvmCompiler.Functions.StackPressureNormalization.Switch.select_normalize]
            cases hSelect : Functions.Source.Switch.select
                value cases defaultBody with
            | none =>
                simp only [Option.map_none, hSelect]
                rfl
            | some selected =>
                simp only [Option.map_some]
                rw [Block.normalize_openRunScoped]
                simp only [hSelect]
                change Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Block.openRunScoped
                      program ctx selected fuel afterScrutinee) _ =
                  Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Block.openRunScoped
                      program ctx selected fuel afterScrutinee) _
                rfl
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
              Functions.Source.Canonical.Stmt.run,
              Functions.Source.Effectful.Control.Stmt.run]
        | succ fuel =>
            simp only [Stmt.normalize]
            unfold Functions.InteractionSemantics.Stmt.openRun
              Functions.Source.Canonical.Stmt.run
              Functions.Source.Effectful.Control.Stmt.run
            let initBase := ctx.withoutLoopControl
            change Simulation.Interaction.bind
                (Functions.InteractionSemantics.Block.openRun
                  (Program.normalize program) initBase fuel
                  (Block.normalize init) state)
                (fun initResult =>
                  match initResult.1.mode with
                  | .regular =>
                      let loopCtx := initResult.2
                      let postBase := initResult.2.withoutLoopControl
                      let bodyBase := initResult.2.withLoopControl
                        initResult.2.scope initResult.2.scope
                      Simulation.Interaction.bind
                        (Functions.InteractionSemantics.Stmt.openRunForLoop
                          (Program.normalize program) loopCtx
                          (Expr.normalize cond) postBase
                          (Block.normalize post) bodyBase
                          (Block.normalize body) fuel initResult.1.state)
                        (fun loopOutcome =>
                          match loopOutcome.mode with
                          | .regular =>
                              Simulation.Interaction.pure
                                (Functions.Source.Effectful.Outcome.regular
                                  (Functions.InteractionSemantics.stateModel.restrictTo
                                    ctx.scope loopOutcome.state), ctx)
                          | .brk | .cont =>
                              Simulation.Interaction.error .InvalidInstruction
                          | .leave | .halt _ =>
                              Simulation.Interaction.pure (loopOutcome, ctx))
                  | .brk | .cont =>
                      Simulation.Interaction.error .InvalidInstruction
                  | .leave | .halt _ =>
                      Simulation.Interaction.pure (initResult.1, ctx)) = _
            rw [Block.normalize_openRun]
            apply Simulation.Interaction.AllDone.bind_congr
              (Simulation.Interaction.AllDone.trivial _)
            intro initResult _
            rcases initResult with ⟨initOutcome, initCtx⟩
            cases hInitMode : initOutcome.mode <;>
              simp only [hInitMode]
            · rw [Stmt.normalize_openRunForLoop]
              apply Simulation.Interaction.AllDone.bind_congr
                (Simulation.Interaction.AllDone.trivial _)
              intro loopOutcome _
              cases hLoopMode : loopOutcome.mode <;>
                simp only [hLoopMode]
              all_goals rfl
            all_goals rfl
    | brk =>
        simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
          Functions.Source.Canonical.Stmt.run,
          Functions.Source.Effectful.Control.Stmt.run]
    | cont =>
        simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
          Functions.Source.Canonical.Stmt.run,
          Functions.Source.Effectful.Control.Stmt.run]
    | leave =>
        simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
          Functions.Source.Canonical.Stmt.run,
          Functions.Source.Effectful.Control.Stmt.run]
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
              Functions.Source.Canonical.Stmt.run,
              Functions.Source.Effectful.Control.Stmt.run]
        | succ fuel =>
            simp only [Stmt.normalize]
            unfold Functions.InteractionSemantics.Stmt.openRun
              Functions.Source.Canonical.Stmt.run
              Functions.Source.Effectful.Control.Stmt.run
            by_cases hTargets : targets.Nodup
            · simp only [hTargets, if_true]
              change Simulation.Interaction.bind
                  (Functions.InteractionSemantics.ArgList.openEval
                    (args.map Expr.normalize) state)
                  (fun argResult =>
                    Simulation.Interaction.bind
                      ((Functions.Source.FunList.find? functionName
                          (Program.normalize program).functions).elim
                        (Simulation.Interaction.error .InvalidInstruction)
                        Simulation.Interaction.pure)
                      (fun fn =>
                        Simulation.Interaction.bind
                          (Functions.InteractionSemantics.FunDef.openRunBody
                            (Program.normalize program) fn argResult.2 fuel
                            argResult.1) _)) = _
              rw [ArgList.normalize_openEval]
              apply Simulation.Interaction.AllDone.bind_congr
                (Simulation.Interaction.AllDone.trivial _)
              intro argResult _
              rcases argResult with ⟨afterArgs, argValues⟩
              simp only [Program.normalize]
              rw [EvmCompiler.Functions.StackPressureNormalization.FunList.find?_normalize]
              cases hFind : Functions.Source.FunList.find?
                  functionName program.functions with
              | none =>
                  simp only [Option.map_none, Option.elim_none]
                  change Simulation.Interaction.bind
                      (Simulation.Interaction.error
                        EvmYul.EVM.ExecutionException.InvalidInstruction) _ =
                    Simulation.Interaction.bind
                      (Simulation.Interaction.error
                        EvmYul.EVM.ExecutionException.InvalidInstruction) _
                  rfl
              | some fn =>
                  simp only [hFind, Option.map_some, Option.elim_some,
                    Simulation.Interaction.bind_done_ok]
                  change Simulation.Interaction.bind
                      (Functions.InteractionSemantics.FunDef.openRunBody
                        (Program.normalize program) (FunDef.normalize fn)
                        argValues fuel afterArgs) _ =
                    Simulation.Interaction.bind
                      (Functions.InteractionSemantics.FunDef.openRunBody
                        program fn argValues fuel afterArgs) _
                  rw [FunDef.normalize_openRunBody]
            · simp [hTargets]
    | terminal kind =>
        simp [Stmt.normalize, Functions.InteractionSemantics.Stmt.openRun,
          Functions.Source.Canonical.Stmt.run,
          Functions.Source.Effectful.Control.Stmt.run]
    | terminalArgs kind args =>
        simp only [Stmt.normalize]
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
          Functions.Source.Effectful.Control.Stmt.run
        change Simulation.Interaction.bind
            (Locals.InteractionSemantics.ExprSeq.openEval
              (ExprSeq.normalize args) state) _ =
          Simulation.Interaction.bind
            (Locals.InteractionSemantics.ExprSeq.openEval args state) _
        rw [ExprSeq.normalize_openEval]
  termination_by (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

theorem Program.normalize_openRunState (fuel : Nat)
    (program : Program) (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Program.openRunState
        fuel (Program.normalize program) state =
      Functions.InteractionSemantics.Program.openRunState
        fuel program state := by
  unfold Functions.InteractionSemantics.Program.openRunState
    Functions.Source.Canonical.Program.runState
    Functions.Source.Effectful.Control.Program.runState
  change Functions.InteractionSemantics.Block.openRunScoped
      (Program.normalize program) Functions.Source.Ctx.initial
      (Block.normalize program.body) fuel state =
    Functions.InteractionSemantics.Block.openRunScoped
      program Functions.Source.Ctx.initial program.body fuel state
  exact Block.normalize_openRunScoped program Functions.Source.Ctx.initial
    program.body fuel state

end EvmCompiler.Functions.StackPressureNormalization
