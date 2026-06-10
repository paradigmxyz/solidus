import EvmCompiler.Core.Except
import EvmCompiler.Expressions.Semantics
import EvmCompiler.Expressions.Compiler
import EvmCompiler.Structured.Preservation

namespace EvmCompiler
namespace Expressions

@[simp] theorem RunState.withEVM_withEVM (state : RunState)
    (first second : EVMState) :
    (state.withEVM first).withEVM second = state.withEVM second := rfl

namespace Structured.Code

theorem run_append (left right : Structured.Code) (state : EVMState) :
    Structured.Code.run (left ++ right) state =
      (do
        let state' ← Structured.Code.run left state
        Structured.Code.run right state') := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [Structured.Code.run, ih]

end Structured.Code

mutual
  theorem Expr.run_eq_compile {results : Nat} (expr : Expr results)
      (state : EVMState) :
      expr.run state = Structured.Code.run expr.compile state := by
    cases expr with
    | lit value =>
        rfl
    | code code =>
        rfl
    | prim op args =>
        simp [Expr.run, Expr.compile, Structured.Code.run_append,
          ExprSeq.run_eq_compile]
        cases hArgs : Structured.Code.run args.compile state with
        | error err =>
            rfl
        | ok state' =>
            cases hStep : op.step state' <;>
              simp [Structured.Code.run, Structured.BasicInstr.step, hStep]

  theorem ExprSeq.run_eq_compile {results : Nat} (exprs : ExprSeq results)
      (state : EVMState) :
      exprs.run state = Structured.Code.run exprs.compile state := by
    cases exprs with
    | nil =>
        rfl
    | cons head tail =>
        simp [ExprSeq.run, ExprSeq.compile, Structured.Code.run_append,
          Expr.run_eq_compile, ExprSeq.run_eq_compile]
end

namespace Expr

theorem runState_eq_compile {results : Nat} (expr : Expr results)
    (state : RunState) :
    expr.runState state = Structured.Code.runState expr.compile state := by
  unfold runState Structured.Code.runState
  rw [Expr.run_eq_compile]

theorem runCondition_eq_compile (cond : Expr 1) (state : EVMState) :
    cond.runCondition state =
      Structured.Code.runCondition cond.compile state := by
  unfold runCondition Structured.Code.runCondition
  rw [Expr.run_eq_compile]
  cases Structured.Code.run cond.compile state <;> rfl

theorem runConditionState_eq_compile (cond : Expr 1) (state : RunState) :
    cond.runConditionState state =
      Structured.Code.runConditionState cond.compile state := by
  unfold runConditionState Structured.Code.runConditionState
  rw [Expr.runCondition_eq_compile]

end Expr

namespace ProcList

theorem lookup?_toStructured (name : Name) (procs : List Proc) :
    Structured.ProcList.lookup? name (ProcList.toStructured procs) =
      Option.map Proc.toStructured (lookup? name procs) := by
  induction procs with
  | nil =>
      rfl
  | cons proc rest ih =>
      unfold lookup? Structured.ProcList.lookup? ProcList.toStructured
      by_cases hName : proc.name = name
      · simp [hName, Proc.toStructured]
      · simp [hName, ih, Proc.toStructured]

theorem lookup?_program_toStructured (name : Name) (program : Program) :
    Structured.ProcList.lookup? name program.toStructured.procs =
      Option.map Proc.toStructured (lookup? name program.procs) := by
  exact lookup?_toStructured name program.procs

end ProcList

namespace Switch

theorem select_toStructured (scrutinee : Word)
    (cases : List (Word × Block)) (defaultBody : Option Block) :
    Structured.Switch.select scrutinee (CaseList.toStructured cases)
        (Default.toStructured defaultBody) =
      Option.map Block.toStructured
        (Switch.select scrutinee cases defaultBody) := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      unfold Switch.select Structured.Switch.select CaseList.toStructured
      by_cases hEq : value = scrutinee
      · simp [hEq]
      · simp [hEq, ih]

end Switch

set_option maxHeartbeats 1200000 in
mutual
  theorem Block.run_toStructured (program : Program) :
      ∀ (fuel : Nat) (block : Block) (state : RunState),
        Block.run program fuel block state =
          Structured.Block.run program.toStructured fuel block.toStructured state := by
    intro fuel block state
    cases fuel with
    | zero =>
        cases block
        rfl
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                rfl
            | cons stmt rest =>
                simp [Block.run, Structured.Block.run, Block.toStructured,
                  StmtList.toStructured]
                rw [Stmt.run_toStructured program fuel stmt state]
                cases hStmt :
                    Structured.Stmt.run program.toStructured fuel
                      stmt.toStructured state with
                | error err =>
                    simp [hStmt]
                | ok outcome =>
                    simp [hStmt]
                    cases outcome.mode <;>
                      simp [Block.toStructured,
                        Block.run_toStructured program fuel
                        { stmts := rest } outcome.state]

  theorem Stmt.runForLoop_toStructured (program : Program)
      (fuel : Nat) (cond : Expr 1) (post body : Block) (state : RunState) :
      Stmt.runForLoop program fuel cond post body state =
        Structured.Stmt.runForLoop program.toStructured fuel cond.compile
          post.toStructured body.toStructured state := by
    cases fuel with
    | zero =>
        rfl
    | succ fuel =>
        unfold Stmt.runForLoop Structured.Stmt.runForLoop
        rw [Expr.runConditionState_eq_compile]
        cases hCond : Structured.Code.runConditionState cond.compile state with
        | error err =>
            simp [hCond]
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            simp [hCond]
            cases condTrue with
            | false =>
                rfl
            | true =>
                rw [Block.run_toStructured program fuel body
                  stateAfterCond]
                cases hBody :
                    Structured.Block.run program.toStructured fuel
                      body.toStructured stateAfterCond with
                | error err =>
                    simp [hBody]
                | ok bodyOutcome =>
                    simp [hBody]
                    cases bodyOutcome.mode with
                    | brk =>
                        rfl
                    | regular =>
                        rw [Block.run_toStructured program fuel post
                          bodyOutcome.state]
                        cases hPost :
                            Structured.Block.run program.toStructured fuel
                              post.toStructured bodyOutcome.state with
                        | error err =>
                            simp [hPost]
                        | ok postOutcome =>
                            simp [hPost, invalid, Structured.invalid]
                            cases postOutcome.mode <;>
                              simp [invalid, Structured.invalid,
                                Stmt.runForLoop_toStructured program fuel
                                cond post body postOutcome.state]
                    | cont =>
                        rw [Block.run_toStructured program fuel post
                          bodyOutcome.state]
                        cases hPost :
                            Structured.Block.run program.toStructured fuel
                              post.toStructured bodyOutcome.state with
                        | error err =>
                            simp [hPost]
                        | ok postOutcome =>
                            simp [hPost, invalid, Structured.invalid]
                            cases postOutcome.mode <;>
                              simp [invalid, Structured.invalid,
                                Stmt.runForLoop_toStructured program fuel
                                cond post body postOutcome.state]
                    | leave =>
                        rfl
                    | halt kind =>
                        rfl

  theorem Stmt.run_toStructured (program : Program) :
      ∀ (fuel : Nat) (stmt : Stmt) (state : RunState),
        Stmt.run program fuel stmt state =
          Structured.Stmt.run program.toStructured fuel stmt.toStructured state := by
    intro fuel stmt state
    cases stmt with
    | code code =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured]
    | expr expr =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured,
          Expr.runState_eq_compile, Structured.Code.runState]
    | if_ cond body =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [Expr.runConditionState_eq_compile]
            cases hCond : Structured.Code.runConditionState cond.compile state with
            | error err =>
                simp [hCond, Except.bind]
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                simp [hCond]
                cases condTrue with
                | false =>
                    rfl
                | true =>
                    exact Block.run_toStructured program fuel body
                      stateAfterCond
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [Expr.run_eq_compile]
            cases hScrutinee :
                Structured.Code.run scrutinee.compile state.evm with
            | error err =>
                simp [hScrutinee, Structured.Code.runState, Except.bind]
            | ok evmAfterScrutinee =>
                simp [hScrutinee, Structured.Code.runState]
                cases hPop : evmAfterScrutinee.stack.pop with
                | none =>
                    simp [hPop]
                | some pair =>
                    rcases pair with ⟨stack, value⟩
                    simp [hPop]
                    rw [Switch.select_toStructured value cases defaultBody]
                    cases hSelected : Switch.select value cases defaultBody with
                    | none =>
                        simp [hSelected]
                    | some selected =>
                        simp [hSelected]
                        exact Block.run_toStructured program fuel selected
                          (state.withEVM { evmAfterScrutinee with stack := stack })
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [Block.run_toStructured program fuel init state]
            cases hInit :
                Structured.Block.run program.toStructured fuel
                  init.toStructured state with
            | error err =>
                simp [hInit]
            | ok initOutcome =>
                simp [hInit]
                cases initOutcome.mode <;>
                  simp [invalid, Structured.invalid,
                    Stmt.runForLoop_toStructured program fuel cond post body
                    initOutcome.state]
    | brk =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured]
    | cont =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured]
    | leave =>
        cases hReturns : state.returns <;>
          simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured,
            invalid, Structured.invalid, hReturns, Outcome.leave,
            Structured.Outcome.leave]
    | call name =>
        cases fuel with
        | zero =>
            rfl
        | succ fuel =>
            unfold Stmt.run Structured.Stmt.run
            simp [Stmt.toStructured]
            rw [ProcList.lookup?_program_toStructured name program]
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                rfl
            | some proc =>
                simp [hLookup, Proc.toStructured]
                cases hSplit :
                    Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hSplit]
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp [hSplit]
                    rw [Block.run_toStructured program fuel proc.body
                      ((state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc)]
                    cases hBody :
                        Structured.Block.run program.toStructured fuel
                          proc.body.toStructured
                          ((state.withEVM { state.evm with stack := args }).pushReturn
                            callerStack proc.retc) with
                    | error err =>
                        simp [hBody]
                    | ok outcome =>
                        simp [hBody, invalid, Structured.invalid]
                        cases outcome.mode <;>
                          simp [hBody, invalid, Structured.invalid]
                        · cases hPop : outcome.state.popReturn? with
                          | none =>
                              simp [hPop, invalid, Structured.invalid]
                          | some pair =>
                              rcases pair with ⟨frame, returned⟩
                              simp [hPop, invalid, Structured.invalid]
                              cases hAttach :
                                  Structured.StackFrame.attachReturns? frame
                                    outcome.state.evm.stack with
                              | none =>
                                  simp [hAttach, invalid, Structured.invalid]
                              | some stack =>
                                  simp [hAttach, invalid, Structured.invalid]
                        · cases hPop : outcome.state.popReturn? with
                          | none =>
                              simp [hPop, invalid, Structured.invalid]
                          | some pair =>
                              rcases pair with ⟨frame, returned⟩
                              simp [hPop, invalid, Structured.invalid]
                              cases hAttach :
                                  Structured.StackFrame.attachReturns? frame
                                    outcome.state.evm.stack with
                              | none =>
                                  simp [hAttach, invalid, Structured.invalid]
                              | some stack =>
                                  simp [hAttach, invalid, Structured.invalid]
    | terminal kind =>
        simp [Stmt.run, Structured.Stmt.run, Stmt.toStructured,
          Structured.Terminal.step]
end

namespace Program

theorem run_toStructured (fuel : Nat) (program : Program) (state : EVMState) :
    program.run fuel state =
      Structured.Program.run fuel program.toStructured state := by
  exact Block.run_toStructured program fuel program.body
    (Structured.Program.initialState state)

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program :=
  Structured.Preservation.ProcedurePreservation.compileChecked?
    program.toStructured

theorem compileChecked?_of_accepted_bounds {program : Program}
    (hAccepted : Program.Accepted program)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        program.toStructured) :
    compileChecked? program = some program.compile := by
  unfold compileChecked?
  simpa [Program.compile] using
    Structured.Preservation.ProcedurePreservation.compileChecked?_of_accepted_bounds
      (program := program.toStructured) hAccepted hBounds

theorem compileChecked?_noCallCreate {program : Program}
    {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  exact
    Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate
      (program := program.toStructured) (asm := asm)
      (by simpa [CompilerFacts.Program.toStructured_usesCallCreate] using
        hProgram)
      hCompile

theorem compile_preserves {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  have hStructuredRun :
      Structured.Program.run fuel program.toStructured initial = .ok outcome := by
    simpa [run_toStructured fuel program initial] using hRun
  exact
    Structured.Preservation.compile_preserves hCompile hInitialPc hStructuredRun

theorem compile_preserves_endPc {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hStructuredRun :
      Structured.Program.run fuel program.toStructured initial = .ok outcome := by
    simpa [run_toStructured fuel program initial] using hRun
  exact
    Structured.Preservation.compile_preserves_endPc hCompile hInitialPc
      hStructuredRun

theorem compile_preserves_checked {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome :=
  compile_preserves hCompile hInitialPc hRun

theorem compile_preserves_checked_endPc {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        program.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome :=
  compile_preserves_endPc hCompile hInitialPc hRun

theorem compile_preserves_of_compileChecked {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  exact compile_preserves_checked hCompile hInitialPc hRun

theorem compile_preserves_of_compileChecked_endPc {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  exact compile_preserves_checked_endPc hCompile hInitialPc hRun

end Program

end Expressions
end EvmCompiler
