import EvmCompiler.Expressions.Compiler
import EvmCompiler.Expressions.InteractionSemantics

namespace EvmCompiler
namespace Expressions
namespace InteractionPreservation

mutual
  theorem Expr.openRun_compile {results : Nat}
      (expr : Expressions.Expr results) (state : Structured.RunState) :
      InteractionSemantics.Expr.openRun expr state =
        Structured.InteractionSemantics.Code.openRun
          expr.compile state := by
    exact Expressions.Expr.rec
      (motive_1 := fun _ expr =>
        ∀ state : Structured.RunState,
          InteractionSemantics.Expr.openRun expr state =
            Structured.InteractionSemantics.Code.openRun
              expr.compile state)
      (motive_2 := fun _ exprs =>
        ∀ state : Structured.RunState,
          InteractionSemantics.ExprSeq.openRun exprs state =
            Structured.InteractionSemantics.Code.openRun
              exprs.compile state)
      (fun value state => by
        simp [InteractionSemantics.Expr.openRun,
          EffectSemantics.Control.Expr.run, Expr.compile,
          Structured.InteractionSemantics.Code.openRun_single,
          Structured.InteractionSemantics.handler])
      (fun code state => by
        rfl)
      (fun op args hArgs state => by
        simp only [InteractionSemantics.Expr.openRun,
          EffectSemantics.Control.Expr.run, Expr.compile,
          Structured.InteractionSemantics.Code.openRun_append]
        change
          Simulation.Interaction.bind
              (InteractionSemantics.ExprSeq.openRun args state)
              (fun middle =>
                Structured.InteractionSemantics.handler.stepInstr
                  (.op op) middle) =
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                args.compile state)
              (Structured.InteractionSemantics.Code.openRun
                [.op op])
        rw [hArgs state]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Structured.InteractionSemantics.Code.openRun
              args.compile state))
        intro middle _
        symm
        exact
          Structured.InteractionSemantics.Code.openRun_single
            (.op op) middle)
      (fun state => by
        rfl)
      (fun head tail hHead hTail state => by
        simp only [InteractionSemantics.ExprSeq.openRun,
          EffectSemantics.Control.ExprSeq.run, ExprSeq.compile,
          Structured.InteractionSemantics.Code.openRun_append]
        change
          Simulation.Interaction.bind
              (InteractionSemantics.Expr.openRun head state)
              (InteractionSemantics.ExprSeq.openRun tail) =
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                head.compile state)
              (Structured.InteractionSemantics.Code.openRun
                tail.compile)
        rw [hHead state]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Structured.InteractionSemantics.Code.openRun
              head.compile state))
        intro middle _
        exact hTail middle)
      expr state

  theorem ExprSeq.openRun_compile {results : Nat}
      (exprs : Expressions.ExprSeq results) (state : Structured.RunState) :
      InteractionSemantics.ExprSeq.openRun exprs state =
        Structured.InteractionSemantics.Code.openRun
          exprs.compile state := by
    exact Expressions.ExprSeq.rec
      (motive_1 := fun _ expr =>
        ∀ state : Structured.RunState,
          InteractionSemantics.Expr.openRun expr state =
            Structured.InteractionSemantics.Code.openRun
              expr.compile state)
      (motive_2 := fun _ exprs =>
        ∀ state : Structured.RunState,
          InteractionSemantics.ExprSeq.openRun exprs state =
            Structured.InteractionSemantics.Code.openRun
              exprs.compile state)
      (fun value state => by
        simp [InteractionSemantics.Expr.openRun,
          EffectSemantics.Control.Expr.run, Expr.compile,
          Structured.InteractionSemantics.Code.openRun_single,
          Structured.InteractionSemantics.handler])
      (fun code state => by
        rfl)
      (fun op args hArgs state => by
        simp only [InteractionSemantics.Expr.openRun,
          EffectSemantics.Control.Expr.run, Expr.compile,
          Structured.InteractionSemantics.Code.openRun_append]
        change
          Simulation.Interaction.bind
              (InteractionSemantics.ExprSeq.openRun args state)
              (fun middle =>
                Structured.InteractionSemantics.handler.stepInstr
                  (.op op) middle) =
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                args.compile state)
              (Structured.InteractionSemantics.Code.openRun
                [.op op])
        rw [hArgs state]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Structured.InteractionSemantics.Code.openRun
              args.compile state))
        intro middle _
        symm
        exact
          Structured.InteractionSemantics.Code.openRun_single
            (.op op) middle)
      (fun state => by
        rfl)
      (fun head tail hHead hTail state => by
        simp only [InteractionSemantics.ExprSeq.openRun,
          EffectSemantics.Control.ExprSeq.run, ExprSeq.compile,
          Structured.InteractionSemantics.Code.openRun_append]
        change
          Simulation.Interaction.bind
              (InteractionSemantics.Expr.openRun head state)
              (InteractionSemantics.ExprSeq.openRun tail) =
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                head.compile state)
              (Structured.InteractionSemantics.Code.openRun
                tail.compile)
        rw [hHead state]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Structured.InteractionSemantics.Code.openRun
              head.compile state))
        intro middle _
        exact hTail middle)
      exprs state

end

theorem Expr.openRunCondition_compile
    (cond : Expressions.Expr 1) (state : Structured.RunState) :
    InteractionSemantics.Expr.openRunCondition cond state =
      Structured.InteractionSemantics.Code.openRunCondition
        cond.compile state := by
  unfold InteractionSemantics.Expr.openRunCondition
    EffectSemantics.Control.Expr.runCondition
    Structured.InteractionSemantics.Code.openRunCondition
    Structured.EffectSemantics.Control.Code.runCondition
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Expr.openRun cond state)
        (Structured.EffectSemantics.Control.Code.popCondition
          Structured.EffectSemantics.Ordinary.runStateModel) =
      Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun
          cond.compile state)
        (Structured.EffectSemantics.Control.Code.popCondition
          Structured.EffectSemantics.Ordinary.runStateModel)
  rw [Expr.openRun_compile]

private theorem lookup?_toStructured
    (name : Name) (procs : List Expressions.Proc) :
    Structured.ProcList.lookup? name
        (Expressions.ProcList.toStructured procs) =
      Option.map Expressions.Proc.toStructured
        (EffectSemantics.ProcList.lookup? name procs) := by
  induction procs with
  | nil =>
      rfl
  | cons proc rest ih =>
      unfold Expressions.ProcList.toStructured
        Structured.ProcList.lookup?
        EffectSemantics.ProcList.lookup?
      by_cases hName : proc.name = name
      · simp [hName]
      · simp [hName, ih]

private theorem select_toStructured
    (value : Word) (cases : List (Word × Expressions.Block))
    (defaultBody : Option Expressions.Block) :
    Option.map Expressions.Block.toStructured
        (EffectSemantics.Switch.select value cases defaultBody) =
      Structured.Switch.select value
        (Expressions.CaseList.toStructured cases)
        (Expressions.Default.toStructured defaultBody) := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons entry rest ih =>
      rcases entry with ⟨caseValue, body⟩
      unfold EffectSemantics.Switch.select
        Expressions.CaseList.toStructured
        Structured.Switch.select
      by_cases hValue : caseValue = value
      · simp [hValue]
      · simp [hValue, ih]

structure ControlPreservesAt (fuel : Nat) : Prop where
  block :
    ∀ (program : Expressions.Program) (block : Expressions.Block)
        (state : Structured.RunState),
      InteractionSemantics.Block.openRun program fuel block state =
        Structured.InteractionSemantics.Block.openRun
          program.toStructured fuel block.toStructured state
  stmt :
    ∀ (program : Expressions.Program) (stmt : Expressions.Stmt)
        (state : Structured.RunState),
      InteractionSemantics.Stmt.openRun program fuel stmt state =
        Structured.InteractionSemantics.Stmt.openRun
          program.toStructured fuel stmt.toStructured state
  loop :
    ∀ (program : Expressions.Program) (cond : Expressions.Expr 1)
        (post body : Expressions.Block) (state : Structured.RunState),
      InteractionSemantics.Stmt.openRunForLoop
          program fuel cond post body state =
        Structured.InteractionSemantics.Stmt.openRunForLoop
          program.toStructured fuel cond.compile
          post.toStructured body.toStructured state

private theorem bind_congr_trivial
    {α β : Type}
    (source : Simulation.Interaction EVMException α)
    (left right : α → Simulation.Interaction EVMException β)
    (hNext : ∀ value, left value = right value) :
    Simulation.Interaction.bind source left =
      Simulation.Interaction.bind source right := by
  exact
    Simulation.Interaction.AllDone.bind_congr
      (Simulation.Interaction.AllDone.trivial source)
      (fun value _ => hNext value)

theorem controlPreservesAt :
    ∀ fuel : Nat, ControlPreservesAt fuel
  | 0 => by
      refine
        { block := ?_
          stmt := ?_
          loop := ?_ }
      · intro program block state
        cases block
        rfl
      · intro program stmt state
        cases stmt with
        | code code =>
            rfl
        | expr expr =>
            unfold InteractionSemantics.Stmt.openRun
              Structured.InteractionSemantics.Stmt.openRun
              EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Control.Stmt.run
            change
              Simulation.Interaction.map
                  Structured.Outcome.regular
                  (InteractionSemantics.Expr.openRun expr state) =
                Simulation.Interaction.map
                  Structured.Outcome.regular
                  (Structured.InteractionSemantics.Code.openRun
                    expr.compile state)
            rw [Expr.openRun_compile]
        | if_ cond body =>
            rfl
        | switch scrutinee cases defaultBody =>
            rfl
        | for_ init cond post body =>
            rfl
        | brk =>
            rfl
        | cont =>
            rfl
        | leave =>
            rfl
        | call name =>
            rfl
        | terminal kind =>
            rfl
      · intro program cond post body state
        rfl
  | fuel + 1 => by
      let ih := controlPreservesAt fuel
      refine
        { block := ?_
          stmt := ?_
          loop := ?_ }
      · intro program block state
        rcases block with ⟨stmts⟩
        cases stmts with
        | nil =>
            rfl
        | cons stmt rest =>
            unfold InteractionSemantics.Block.openRun
              Structured.InteractionSemantics.Block.openRun
              EffectSemantics.Control.Block.run
              Structured.EffectSemantics.Control.Block.run
            change
              Simulation.Interaction.bind
                  (InteractionSemantics.Stmt.openRun
                    program fuel stmt state)
                  (fun outcome =>
                    match outcome.mode with
                    | .regular =>
                        InteractionSemantics.Block.openRun
                          program fuel ⟨rest⟩ outcome.state
                    | .brk | .cont | .leave | .halt _ =>
                        pure outcome) =
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Stmt.openRun
                    program.toStructured fuel stmt.toStructured state)
                  (fun outcome =>
                    match outcome.mode with
                    | .regular =>
                        Structured.InteractionSemantics.Block.openRun
                          program.toStructured fuel
                          ⟨Expressions.StmtList.toStructured rest⟩
                          outcome.state
                    | .brk | .cont | .leave | .halt _ =>
                        pure outcome)
            rw [ih.stmt program stmt state]
            apply bind_congr_trivial
            intro outcome
            cases outcome.mode with
            | regular =>
                exact ih.block program ⟨rest⟩ outcome.state
            | brk | cont | leave | halt =>
                rfl
      · intro program stmt state
        cases stmt with
        | code code =>
            rfl
        | expr expr =>
            unfold InteractionSemantics.Stmt.openRun
              Structured.InteractionSemantics.Stmt.openRun
              EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Control.Stmt.run
            change
              Simulation.Interaction.map
                  Structured.Outcome.regular
                  (InteractionSemantics.Expr.openRun expr state) =
                Simulation.Interaction.map
                  Structured.Outcome.regular
                  (Structured.InteractionSemantics.Code.openRun
                    expr.compile state)
            rw [Expr.openRun_compile]
        | if_ cond body =>
            unfold InteractionSemantics.Stmt.openRun
              Structured.InteractionSemantics.Stmt.openRun
              EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Control.Stmt.run
            change
              Simulation.Interaction.bind
                  (InteractionSemantics.Expr.openRunCondition cond state)
                  (fun result =>
                    if result.2 then
                      InteractionSemantics.Block.openRun
                        program fuel body result.1
                    else
                      pure (Structured.Outcome.regular result.1)) =
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRunCondition
                    cond.compile state)
                  (fun result =>
                    if result.2 then
                      Structured.InteractionSemantics.Block.openRun
                        program.toStructured fuel body.toStructured result.1
                    else
                      pure (Structured.Outcome.regular result.1))
            rw [Expr.openRunCondition_compile]
            apply bind_congr_trivial
            intro result
            cases result with
            | mk afterCond condTrue =>
                cases condTrue with
                | false => rfl
                | true => exact ih.block program body afterCond
        | switch scrutinee cases defaultBody =>
            unfold InteractionSemantics.Stmt.openRun
              Structured.InteractionSemantics.Stmt.openRun
              EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Control.Stmt.run
            change
              Simulation.Interaction.bind
                  (InteractionSemantics.Expr.openRun scrutinee state)
                  _ =
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    scrutinee.compile state)
                  _
            rw [Expr.openRun_compile]
            apply bind_congr_trivial
            intro afterScrutinee
            simp only [
              Structured.EffectSemantics.Ordinary.runStateModel_evm,
              Structured.EffectSemantics.Ordinary.runStateModel_withEVM]
            cases hPop : afterScrutinee.evm.stack.pop with
            | none =>
                rfl
            | some popped =>
                rcases popped with ⟨stack, value⟩
                have hSelect :=
                  select_toStructured value cases defaultBody
                cases hSource :
                    EffectSemantics.Switch.select
                      value cases defaultBody with
                | none =>
                    have hTarget :
                        Structured.Switch.select value
                            (Expressions.CaseList.toStructured cases)
                            (Expressions.Default.toStructured defaultBody) =
                          none := by
                      simpa [hSource] using hSelect.symm
                    simp [hPop, hSource, hTarget]
                | some selected =>
                    have hTarget :
                        Structured.Switch.select value
                            (Expressions.CaseList.toStructured cases)
                            (Expressions.Default.toStructured defaultBody) =
                          some selected.toStructured := by
                      simpa [hSource] using hSelect.symm
                    simp only [hPop, hSource, hTarget]
                    exact
                      ih.block program selected
                        (afterScrutinee.withEVM
                          { afterScrutinee.evm with stack := stack })
        | for_ init cond post body =>
            unfold InteractionSemantics.Stmt.openRun
              Structured.InteractionSemantics.Stmt.openRun
              EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Control.Stmt.run
            change
              Simulation.Interaction.bind
                  (InteractionSemantics.Block.openRun
                    program fuel init state)
                  _ =
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Block.openRun
                    program.toStructured fuel init.toStructured state)
                  _
            rw [ih.block program init state]
            apply bind_congr_trivial
            intro outcome
            rcases outcome with ⟨outState, mode⟩
            cases mode with
            | regular =>
                exact ih.loop program cond post body outState
            | brk | cont | leave | halt =>
                rfl
        | brk =>
            rfl
        | cont =>
            rfl
        | leave =>
            rfl
        | call name =>
            unfold InteractionSemantics.Stmt.openRun
              Structured.InteractionSemantics.Stmt.openRun
              EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Control.Stmt.run
            simp only [Expressions.Stmt.toStructured,
              Expressions.Program.toStructured]
            rw [lookup?_toStructured]
            cases hLookup :
                EffectSemantics.ProcList.lookup?
                  name program.procs with
            | none =>
                simp [hLookup]
            | some proc =>
                simp only [hLookup, Option.map_some,
                  Expressions.Proc.toStructured]
                cases hSplit :
                    Structured.StackFrame.splitArgs?
                      proc.argc state.evm.stack with
                | none =>
                    simp [hSplit]
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp only [hSplit,
                      Structured.EffectSemantics.Ordinary.runStateModel_evm,
                      Structured.EffectSemantics.Ordinary.runStateModel_withEVM,
                      Structured.EffectSemantics.Ordinary.runStateModel_pushReturn]
                    change
                      Simulation.Interaction.bind
                          (InteractionSemantics.Block.openRun
                            program fuel proc.body
                            ((state.withEVM
                              { state.evm with stack := args }).pushReturn
                              callerStack proc.retc))
                          _ =
                        Simulation.Interaction.bind
                          (Structured.InteractionSemantics.Block.openRun
                            program.toStructured fuel
                            proc.body.toStructured
                            ((state.withEVM
                              { state.evm with stack := args }).pushReturn
                              callerStack proc.retc))
                          _
                    rw [ih.block program proc.body
                      ((state.withEVM
                        { state.evm with stack := args }).pushReturn
                        callerStack proc.retc)]
                    apply bind_congr_trivial
                    intro outcome
                    simp only [
                      Structured.EffectSemantics.Ordinary.runStateModel_popReturn?]
                    rcases outcome with ⟨outState, outMode⟩
                    cases outMode <;> rfl
        | terminal kind =>
            rfl
      · intro program cond post body state
        unfold InteractionSemantics.Stmt.openRunForLoop
          Structured.InteractionSemantics.Stmt.openRunForLoop
          EffectSemantics.Control.Stmt.runForLoop
          Structured.EffectSemantics.Control.Stmt.runForLoop
        change
          Simulation.Interaction.bind
              (InteractionSemantics.Expr.openRunCondition cond state)
              _ =
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRunCondition
                cond.compile state)
              _
        rw [Expr.openRunCondition_compile]
        apply bind_congr_trivial
        intro result
        rcases result with ⟨stateAfterCond, condTrue⟩
        cases condTrue with
        | false =>
            rfl
        | true =>
            change
              Simulation.Interaction.bind
                  (InteractionSemantics.Block.openRun
                    program fuel body stateAfterCond)
                  _ =
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Block.openRun
                    program.toStructured fuel body.toStructured
                    stateAfterCond)
                  _
            rw [ih.block program body stateAfterCond]
            apply bind_congr_trivial
            intro bodyOutcome
            rcases bodyOutcome with ⟨bodyState, bodyMode⟩
            cases bodyMode with
            | brk =>
                rfl
            | leave | halt =>
                rfl
            | regular | cont =>
                change
                  Simulation.Interaction.bind
                      (InteractionSemantics.Block.openRun
                        program fuel post bodyState)
                      _ =
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Block.openRun
                        program.toStructured fuel post.toStructured
                        bodyState)
                      _
                rw [ih.block program post bodyState]
                apply bind_congr_trivial
                intro postOutcome
                rcases postOutcome with ⟨postState, postMode⟩
                cases postMode with
                | regular =>
                    exact
                      ih.loop program cond post body postState
                | brk | cont | leave | halt =>
                    rfl

theorem Block.openRun_toStructured
    (program : Expressions.Program) (fuel : Nat)
    (block : Expressions.Block) (state : Structured.RunState) :
    InteractionSemantics.Block.openRun program fuel block state =
      Structured.InteractionSemantics.Block.openRun
        program.toStructured fuel block.toStructured state :=
  (controlPreservesAt fuel).block program block state

theorem Stmt.openRun_toStructured
    (program : Expressions.Program) (fuel : Nat)
    (stmt : Expressions.Stmt) (state : Structured.RunState) :
    InteractionSemantics.Stmt.openRun program fuel stmt state =
      Structured.InteractionSemantics.Stmt.openRun
        program.toStructured fuel stmt.toStructured state :=
  (controlPreservesAt fuel).stmt program stmt state

theorem Stmt.openRunForLoop_toStructured
    (program : Expressions.Program) (fuel : Nat)
    (cond : Expressions.Expr 1) (post body : Expressions.Block)
    (state : Structured.RunState) :
    InteractionSemantics.Stmt.openRunForLoop
        program fuel cond post body state =
      Structured.InteractionSemantics.Stmt.openRunForLoop
        program.toStructured fuel cond.compile
        post.toStructured body.toStructured state :=
  (controlPreservesAt fuel).loop program cond post body state

theorem Program.openRunState_toStructured
    (fuel : Nat) (program : Expressions.Program)
    (state : Structured.RunState) :
    InteractionSemantics.Program.openRunState fuel program state =
      Structured.InteractionSemantics.Program.openRunState
        fuel program.toStructured state := by
  exact Block.openRun_toStructured program fuel program.body state

theorem Program.openRun_toStructured
    (fuel : Nat) (program : Expressions.Program)
    (state : EVMState) :
    InteractionSemantics.Program.openRun fuel program state =
      Structured.InteractionSemantics.Program.openRun
        fuel program.toStructured state := by
  exact
    Program.openRunState_toStructured
      fuel program (Structured.Program.initialState state)

end InteractionPreservation
end Expressions
end EvmCompiler
